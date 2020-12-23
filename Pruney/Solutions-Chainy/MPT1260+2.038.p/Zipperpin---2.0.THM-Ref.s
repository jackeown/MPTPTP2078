%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ETa6yzIxEO

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:28 EST 2020

% Result     : Theorem 32.45s
% Output     : Refutation 32.45s
% Verified   : 
% Statistics : Number of formulae       :  297 (2326 expanded)
%              Number of leaves         :   46 ( 734 expanded)
%              Depth                    :   23
%              Number of atoms          : 2717 (24195 expanded)
%              Number of equality atoms :  211 (1668 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t76_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X69: $i,X70: $i,X71: $i] :
      ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X70 ) ) )
      | ~ ( v3_pre_topc @ X69 @ X70 )
      | ~ ( r1_tarski @ X69 @ X71 )
      | ( r1_tarski @ X69 @ ( k1_tops_1 @ X70 @ X71 ) )
      | ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X70 ) ) )
      | ~ ( l1_pre_topc @ X70 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_tarski @ sk_B_1 @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X76: $i,X77: $i] :
      ( ~ ( m1_subset_1 @ X76 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X77 ) ) )
      | ( ( k1_tops_1 @ X77 @ X76 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X77 ) @ X76 @ ( k2_tops_1 @ X77 @ X76 ) ) )
      | ~ ( l1_pre_topc @ X77 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) )
      | ( ( k7_subset_1 @ X49 @ X48 @ X50 )
        = ( k4_xboole_0 @ X48 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('32',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X68 ) ) )
      | ( ( k2_tops_1 @ X68 @ X67 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X68 ) @ ( k2_pre_topc @ X68 @ X67 ) @ ( k1_tops_1 @ X68 @ X67 ) ) )
      | ~ ( l1_pre_topc @ X68 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('37',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( l1_pre_topc @ X61 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X61 @ X62 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) )
      | ( ( k7_subset_1 @ X49 @ X48 @ X50 )
        = ( k4_xboole_0 @ X48 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['35','42'])).

thf('44',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['30','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('46',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('51',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('53',plain,
    ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('56',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('58',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X35 @ X36 )
        = ( k4_xboole_0 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('59',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('61',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('62',plain,(
    ! [X58: $i,X60: $i] :
      ( ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X60 ) )
      | ~ ( r1_tarski @ X58 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X35 @ X36 )
        = ( k4_xboole_0 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('65',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('67',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_subset_1 @ X44 @ ( k3_subset_1 @ X44 @ X43 ) )
        = X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('68',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_tarski @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('73',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','73'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('75',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k3_xboole_0 @ X32 @ X33 ) )
      = ( k4_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('76',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ ( k3_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    r1_tarski @ sk_B_1 @ ( k3_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('80',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('82',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('83',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X58: $i,X60: $i] :
      ( ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X60 ) )
      | ~ ( r1_tarski @ X58 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','88'])).

thf('90',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_tarski @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( sk_B_1
    = ( k3_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','93'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('95',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('96',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['94','97'])).

thf('99',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('100',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['69','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('103',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( l1_pre_topc @ X63 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X63 @ X64 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('104',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('108',plain,(
    ! [X58: $i,X60: $i] :
      ( ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X60 ) )
      | ~ ( r1_tarski @ X58 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('110',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X46 ) )
      | ( ( k4_subset_1 @ X46 @ X45 @ X47 )
        = ( k2_xboole_0 @ X45 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['101','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('117',plain,(
    ! [X74: $i,X75: $i] :
      ( ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X75 ) ) )
      | ( ( k2_pre_topc @ X75 @ X74 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X75 ) @ X74 @ ( k2_tops_1 @ X75 @ X74 ) ) )
      | ~ ( l1_pre_topc @ X75 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('118',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['69','100'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('123',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['115','120','121','122'])).

thf('124',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['56','123'])).

thf('125',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('126',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k3_xboole_0 @ X32 @ X33 ) )
      = ( k4_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('127',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('130',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['125','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('135',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['132','133','136'])).

thf('138',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','88'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_subset_1 @ X44 @ ( k3_subset_1 @ X44 @ X43 ) )
        = X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['137','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['132','133','136'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('148',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['151','152','153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['146','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','87'])).

thf('159',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X35 @ X36 )
        = ( k4_xboole_0 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['157','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['156','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('164',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('165',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['166','167','168','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['162','163','170','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['145','179'])).

thf('181',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['124','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('183',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['56','123'])).

thf('184',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['115','120','121','122'])).

thf('185',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('186',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('187',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['185','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('195',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('196',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['193','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['192','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['191','198'])).

thf('200',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['184','199'])).

thf('201',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('202',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['132','133','136'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['202','205'])).

thf('207',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['35','42'])).

thf('208',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('209',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['206','207','208'])).

thf('210',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k1_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['181','182','183','209'])).

thf('211',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['115','120','121','122'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('213',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('214',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('216',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k2_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['214','215'])).

thf('217',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k2_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['211','216'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('219',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('220',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['212','213'])).

thf('221',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k2_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['211','216'])).

thf('222',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['115','120','121','122'])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('225',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_subset_1 @ X44 @ ( k3_subset_1 @ X44 @ X43 ) )
        = X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('227',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['115','120','121','122'])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('231',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X35 @ X36 )
        = ( k4_xboole_0 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['229','232'])).

thf('234',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['228','233'])).

thf('235',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['115','120','121','122'])).

thf('236',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['227','236'])).

thf('238',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['222','237'])).

thf('239',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['210','238'])).

thf('240',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('241',plain,(
    ! [X65: $i,X66: $i] :
      ( ~ ( l1_pre_topc @ X65 )
      | ~ ( v2_pre_topc @ X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X65 @ X66 ) @ X65 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('242',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['242','243','244'])).

thf('246',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['239','245'])).

thf('247',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('248',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','49','50','248'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ETa6yzIxEO
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 32.45/32.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 32.45/32.63  % Solved by: fo/fo7.sh
% 32.45/32.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 32.45/32.63  % done 45302 iterations in 32.132s
% 32.45/32.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 32.45/32.63  % SZS output start Refutation
% 32.45/32.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 32.45/32.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 32.45/32.63  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 32.45/32.63  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 32.45/32.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 32.45/32.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 32.45/32.63  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 32.45/32.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 32.45/32.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 32.45/32.63  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 32.45/32.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 32.45/32.63  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 32.45/32.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 32.45/32.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 32.45/32.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 32.45/32.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 32.45/32.63  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 32.45/32.63  thf(sk_A_type, type, sk_A: $i).
% 32.45/32.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 32.45/32.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 32.45/32.63  thf(t76_tops_1, conjecture,
% 32.45/32.63    (![A:$i]:
% 32.45/32.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 32.45/32.63       ( ![B:$i]:
% 32.45/32.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 32.45/32.63           ( ( v3_pre_topc @ B @ A ) <=>
% 32.45/32.63             ( ( k2_tops_1 @ A @ B ) =
% 32.45/32.63               ( k7_subset_1 @
% 32.45/32.63                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 32.45/32.63  thf(zf_stmt_0, negated_conjecture,
% 32.45/32.63    (~( ![A:$i]:
% 32.45/32.63        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 32.45/32.63          ( ![B:$i]:
% 32.45/32.63            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 32.45/32.63              ( ( v3_pre_topc @ B @ A ) <=>
% 32.45/32.63                ( ( k2_tops_1 @ A @ B ) =
% 32.45/32.63                  ( k7_subset_1 @
% 32.45/32.63                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 32.45/32.63    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 32.45/32.63  thf('0', plain,
% 32.45/32.63      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 32.45/32.63        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf('1', plain,
% 32.45/32.63      (~
% 32.45/32.63       (((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 32.45/32.63       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 32.45/32.63      inference('split', [status(esa)], ['0'])).
% 32.45/32.63  thf('2', plain,
% 32.45/32.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf('3', plain,
% 32.45/32.63      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 32.45/32.63        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf('4', plain,
% 32.45/32.63      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 32.45/32.63      inference('split', [status(esa)], ['3'])).
% 32.45/32.63  thf('5', plain,
% 32.45/32.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf(t56_tops_1, axiom,
% 32.45/32.63    (![A:$i]:
% 32.45/32.63     ( ( l1_pre_topc @ A ) =>
% 32.45/32.63       ( ![B:$i]:
% 32.45/32.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 32.45/32.63           ( ![C:$i]:
% 32.45/32.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 32.45/32.63               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 32.45/32.63                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 32.45/32.63  thf('6', plain,
% 32.45/32.63      (![X69 : $i, X70 : $i, X71 : $i]:
% 32.45/32.63         (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ X70)))
% 32.45/32.63          | ~ (v3_pre_topc @ X69 @ X70)
% 32.45/32.63          | ~ (r1_tarski @ X69 @ X71)
% 32.45/32.63          | (r1_tarski @ X69 @ (k1_tops_1 @ X70 @ X71))
% 32.45/32.63          | ~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (u1_struct_0 @ X70)))
% 32.45/32.63          | ~ (l1_pre_topc @ X70))),
% 32.45/32.63      inference('cnf', [status(esa)], [t56_tops_1])).
% 32.45/32.63  thf('7', plain,
% 32.45/32.63      (![X0 : $i]:
% 32.45/32.63         (~ (l1_pre_topc @ sk_A)
% 32.45/32.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 32.45/32.63          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 32.45/32.63          | ~ (r1_tarski @ sk_B_1 @ X0)
% 32.45/32.63          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 32.45/32.63      inference('sup-', [status(thm)], ['5', '6'])).
% 32.45/32.63  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf('9', plain,
% 32.45/32.63      (![X0 : $i]:
% 32.45/32.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 32.45/32.63          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 32.45/32.63          | ~ (r1_tarski @ sk_B_1 @ X0)
% 32.45/32.63          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 32.45/32.63      inference('demod', [status(thm)], ['7', '8'])).
% 32.45/32.63  thf('10', plain,
% 32.45/32.63      ((![X0 : $i]:
% 32.45/32.63          (~ (r1_tarski @ sk_B_1 @ X0)
% 32.45/32.63           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 32.45/32.63           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 32.45/32.63         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 32.45/32.63      inference('sup-', [status(thm)], ['4', '9'])).
% 32.45/32.63  thf('11', plain,
% 32.45/32.63      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 32.45/32.63         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 32.45/32.63         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 32.45/32.63      inference('sup-', [status(thm)], ['2', '10'])).
% 32.45/32.63  thf(d10_xboole_0, axiom,
% 32.45/32.63    (![A:$i,B:$i]:
% 32.45/32.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 32.45/32.63  thf('12', plain,
% 32.45/32.63      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 32.45/32.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 32.45/32.63  thf('13', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 32.45/32.63      inference('simplify', [status(thm)], ['12'])).
% 32.45/32.63  thf('14', plain,
% 32.45/32.63      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 32.45/32.63         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 32.45/32.63      inference('demod', [status(thm)], ['11', '13'])).
% 32.45/32.63  thf('15', plain,
% 32.45/32.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf(t74_tops_1, axiom,
% 32.45/32.63    (![A:$i]:
% 32.45/32.63     ( ( l1_pre_topc @ A ) =>
% 32.45/32.63       ( ![B:$i]:
% 32.45/32.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 32.45/32.63           ( ( k1_tops_1 @ A @ B ) =
% 32.45/32.63             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 32.45/32.63  thf('16', plain,
% 32.45/32.63      (![X76 : $i, X77 : $i]:
% 32.45/32.63         (~ (m1_subset_1 @ X76 @ (k1_zfmisc_1 @ (u1_struct_0 @ X77)))
% 32.45/32.63          | ((k1_tops_1 @ X77 @ X76)
% 32.45/32.63              = (k7_subset_1 @ (u1_struct_0 @ X77) @ X76 @ 
% 32.45/32.63                 (k2_tops_1 @ X77 @ X76)))
% 32.45/32.63          | ~ (l1_pre_topc @ X77))),
% 32.45/32.63      inference('cnf', [status(esa)], [t74_tops_1])).
% 32.45/32.63  thf('17', plain,
% 32.45/32.63      ((~ (l1_pre_topc @ sk_A)
% 32.45/32.63        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 32.45/32.63               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 32.45/32.63      inference('sup-', [status(thm)], ['15', '16'])).
% 32.45/32.63  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf('19', plain,
% 32.45/32.63      (((k1_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 32.45/32.63            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['17', '18'])).
% 32.45/32.63  thf('20', plain,
% 32.45/32.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf(redefinition_k7_subset_1, axiom,
% 32.45/32.63    (![A:$i,B:$i,C:$i]:
% 32.45/32.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 32.45/32.63       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 32.45/32.63  thf('21', plain,
% 32.45/32.63      (![X48 : $i, X49 : $i, X50 : $i]:
% 32.45/32.63         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49))
% 32.45/32.63          | ((k7_subset_1 @ X49 @ X48 @ X50) = (k4_xboole_0 @ X48 @ X50)))),
% 32.45/32.63      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 32.45/32.63  thf('22', plain,
% 32.45/32.63      (![X0 : $i]:
% 32.45/32.63         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 32.45/32.63           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 32.45/32.63      inference('sup-', [status(thm)], ['20', '21'])).
% 32.45/32.63  thf('23', plain,
% 32.45/32.63      (((k1_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['19', '22'])).
% 32.45/32.63  thf(t36_xboole_1, axiom,
% 32.45/32.63    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 32.45/32.63  thf('24', plain,
% 32.45/32.63      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 32.45/32.63      inference('cnf', [status(esa)], [t36_xboole_1])).
% 32.45/32.63  thf('25', plain,
% 32.45/32.63      (![X4 : $i, X6 : $i]:
% 32.45/32.63         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 32.45/32.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 32.45/32.63  thf('26', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 32.45/32.63          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 32.45/32.63      inference('sup-', [status(thm)], ['24', '25'])).
% 32.45/32.63  thf('27', plain,
% 32.45/32.63      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 32.45/32.63        | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 32.45/32.63      inference('sup-', [status(thm)], ['23', '26'])).
% 32.45/32.63  thf('28', plain,
% 32.45/32.63      (((k1_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['19', '22'])).
% 32.45/32.63  thf('29', plain,
% 32.45/32.63      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 32.45/32.63        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['27', '28'])).
% 32.45/32.63  thf('30', plain,
% 32.45/32.63      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 32.45/32.63         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 32.45/32.63      inference('sup-', [status(thm)], ['14', '29'])).
% 32.45/32.63  thf('31', plain,
% 32.45/32.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf(l78_tops_1, axiom,
% 32.45/32.63    (![A:$i]:
% 32.45/32.63     ( ( l1_pre_topc @ A ) =>
% 32.45/32.63       ( ![B:$i]:
% 32.45/32.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 32.45/32.63           ( ( k2_tops_1 @ A @ B ) =
% 32.45/32.63             ( k7_subset_1 @
% 32.45/32.63               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 32.45/32.63               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 32.45/32.63  thf('32', plain,
% 32.45/32.63      (![X67 : $i, X68 : $i]:
% 32.45/32.63         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (u1_struct_0 @ X68)))
% 32.45/32.63          | ((k2_tops_1 @ X68 @ X67)
% 32.45/32.63              = (k7_subset_1 @ (u1_struct_0 @ X68) @ 
% 32.45/32.63                 (k2_pre_topc @ X68 @ X67) @ (k1_tops_1 @ X68 @ X67)))
% 32.45/32.63          | ~ (l1_pre_topc @ X68))),
% 32.45/32.63      inference('cnf', [status(esa)], [l78_tops_1])).
% 32.45/32.63  thf('33', plain,
% 32.45/32.63      ((~ (l1_pre_topc @ sk_A)
% 32.45/32.63        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 32.45/32.63      inference('sup-', [status(thm)], ['31', '32'])).
% 32.45/32.63  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf('35', plain,
% 32.45/32.63      (((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['33', '34'])).
% 32.45/32.63  thf('36', plain,
% 32.45/32.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf(dt_k2_pre_topc, axiom,
% 32.45/32.63    (![A:$i,B:$i]:
% 32.45/32.63     ( ( ( l1_pre_topc @ A ) & 
% 32.45/32.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 32.45/32.63       ( m1_subset_1 @
% 32.45/32.63         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 32.45/32.63  thf('37', plain,
% 32.45/32.63      (![X61 : $i, X62 : $i]:
% 32.45/32.63         (~ (l1_pre_topc @ X61)
% 32.45/32.63          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 32.45/32.63          | (m1_subset_1 @ (k2_pre_topc @ X61 @ X62) @ 
% 32.45/32.63             (k1_zfmisc_1 @ (u1_struct_0 @ X61))))),
% 32.45/32.63      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 32.45/32.63  thf('38', plain,
% 32.45/32.63      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 32.45/32.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 32.45/32.63        | ~ (l1_pre_topc @ sk_A))),
% 32.45/32.63      inference('sup-', [status(thm)], ['36', '37'])).
% 32.45/32.63  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf('40', plain,
% 32.45/32.63      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 32.45/32.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('demod', [status(thm)], ['38', '39'])).
% 32.45/32.63  thf('41', plain,
% 32.45/32.63      (![X48 : $i, X49 : $i, X50 : $i]:
% 32.45/32.63         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49))
% 32.45/32.63          | ((k7_subset_1 @ X49 @ X48 @ X50) = (k4_xboole_0 @ X48 @ X50)))),
% 32.45/32.63      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 32.45/32.63  thf('42', plain,
% 32.45/32.63      (![X0 : $i]:
% 32.45/32.63         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 32.45/32.63           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 32.45/32.63      inference('sup-', [status(thm)], ['40', '41'])).
% 32.45/32.63  thf('43', plain,
% 32.45/32.63      (((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 32.45/32.63            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['35', '42'])).
% 32.45/32.63  thf('44', plain,
% 32.45/32.63      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 32.45/32.63         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 32.45/32.63      inference('sup+', [status(thm)], ['30', '43'])).
% 32.45/32.63  thf('45', plain,
% 32.45/32.63      (![X0 : $i]:
% 32.45/32.63         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 32.45/32.63           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 32.45/32.63      inference('sup-', [status(thm)], ['40', '41'])).
% 32.45/32.63  thf('46', plain,
% 32.45/32.63      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 32.45/32.63         <= (~
% 32.45/32.63             (((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 32.45/32.63      inference('split', [status(esa)], ['0'])).
% 32.45/32.63  thf('47', plain,
% 32.45/32.63      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 32.45/32.63         <= (~
% 32.45/32.63             (((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 32.45/32.63      inference('sup-', [status(thm)], ['45', '46'])).
% 32.45/32.63  thf('48', plain,
% 32.45/32.63      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 32.45/32.63         <= (~
% 32.45/32.63             (((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 32.45/32.63             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 32.45/32.63      inference('sup-', [status(thm)], ['44', '47'])).
% 32.45/32.63  thf('49', plain,
% 32.45/32.63      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 32.45/32.63       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 32.45/32.63      inference('simplify', [status(thm)], ['48'])).
% 32.45/32.63  thf('50', plain,
% 32.45/32.63      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 32.45/32.63       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 32.45/32.63      inference('split', [status(esa)], ['3'])).
% 32.45/32.63  thf('51', plain,
% 32.45/32.63      (((k1_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['19', '22'])).
% 32.45/32.63  thf(t39_xboole_1, axiom,
% 32.45/32.63    (![A:$i,B:$i]:
% 32.45/32.63     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 32.45/32.63  thf('52', plain,
% 32.45/32.63      (![X22 : $i, X23 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 32.45/32.63           = (k2_xboole_0 @ X22 @ X23))),
% 32.45/32.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 32.45/32.63  thf('53', plain,
% 32.45/32.63      (((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 32.45/32.63         (k1_tops_1 @ sk_A @ sk_B_1))
% 32.45/32.63         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 32.45/32.63      inference('sup+', [status(thm)], ['51', '52'])).
% 32.45/32.63  thf(commutativity_k2_xboole_0, axiom,
% 32.45/32.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 32.45/32.63  thf('54', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('55', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('56', plain,
% 32.45/32.63      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 32.45/32.63         (k2_tops_1 @ sk_A @ sk_B_1))
% 32.45/32.63         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['53', '54', '55'])).
% 32.45/32.63  thf('57', plain,
% 32.45/32.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf(d5_subset_1, axiom,
% 32.45/32.63    (![A:$i,B:$i]:
% 32.45/32.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 32.45/32.63       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 32.45/32.63  thf('58', plain,
% 32.45/32.63      (![X35 : $i, X36 : $i]:
% 32.45/32.63         (((k3_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))
% 32.45/32.63          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 32.45/32.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 32.45/32.63  thf('59', plain,
% 32.45/32.63      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 32.45/32.63         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 32.45/32.63      inference('sup-', [status(thm)], ['57', '58'])).
% 32.45/32.63  thf('60', plain,
% 32.45/32.63      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 32.45/32.63      inference('cnf', [status(esa)], [t36_xboole_1])).
% 32.45/32.63  thf('61', plain,
% 32.45/32.63      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 32.45/32.63        (u1_struct_0 @ sk_A))),
% 32.45/32.63      inference('sup+', [status(thm)], ['59', '60'])).
% 32.45/32.63  thf(t3_subset, axiom,
% 32.45/32.63    (![A:$i,B:$i]:
% 32.45/32.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 32.45/32.63  thf('62', plain,
% 32.45/32.63      (![X58 : $i, X60 : $i]:
% 32.45/32.63         ((m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X60)) | ~ (r1_tarski @ X58 @ X60))),
% 32.45/32.63      inference('cnf', [status(esa)], [t3_subset])).
% 32.45/32.63  thf('63', plain,
% 32.45/32.63      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 32.45/32.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('sup-', [status(thm)], ['61', '62'])).
% 32.45/32.63  thf('64', plain,
% 32.45/32.63      (![X35 : $i, X36 : $i]:
% 32.45/32.63         (((k3_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))
% 32.45/32.63          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 32.45/32.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 32.45/32.63  thf('65', plain,
% 32.45/32.63      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 32.45/32.63         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 32.45/32.63      inference('sup-', [status(thm)], ['63', '64'])).
% 32.45/32.63  thf('66', plain,
% 32.45/32.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf(involutiveness_k3_subset_1, axiom,
% 32.45/32.63    (![A:$i,B:$i]:
% 32.45/32.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 32.45/32.63       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 32.45/32.63  thf('67', plain,
% 32.45/32.63      (![X43 : $i, X44 : $i]:
% 32.45/32.63         (((k3_subset_1 @ X44 @ (k3_subset_1 @ X44 @ X43)) = (X43))
% 32.45/32.63          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 32.45/32.63      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 32.45/32.63  thf('68', plain,
% 32.45/32.63      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 32.45/32.63      inference('sup-', [status(thm)], ['66', '67'])).
% 32.45/32.63  thf('69', plain,
% 32.45/32.63      (((sk_B_1)
% 32.45/32.63         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['65', '68'])).
% 32.45/32.63  thf('70', plain,
% 32.45/32.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf('71', plain,
% 32.45/32.63      (![X58 : $i, X59 : $i]:
% 32.45/32.63         ((r1_tarski @ X58 @ X59) | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X59)))),
% 32.45/32.63      inference('cnf', [status(esa)], [t3_subset])).
% 32.45/32.63  thf('72', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 32.45/32.63      inference('sup-', [status(thm)], ['70', '71'])).
% 32.45/32.63  thf(l32_xboole_1, axiom,
% 32.45/32.63    (![A:$i,B:$i]:
% 32.45/32.63     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 32.45/32.63  thf('73', plain,
% 32.45/32.63      (![X7 : $i, X9 : $i]:
% 32.45/32.63         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 32.45/32.63      inference('cnf', [status(esa)], [l32_xboole_1])).
% 32.45/32.63  thf('74', plain,
% 32.45/32.63      (((k4_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 32.45/32.63      inference('sup-', [status(thm)], ['72', '73'])).
% 32.45/32.63  thf(t47_xboole_1, axiom,
% 32.45/32.63    (![A:$i,B:$i]:
% 32.45/32.63     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 32.45/32.63  thf('75', plain,
% 32.45/32.63      (![X32 : $i, X33 : $i]:
% 32.45/32.63         ((k4_xboole_0 @ X32 @ (k3_xboole_0 @ X32 @ X33))
% 32.45/32.63           = (k4_xboole_0 @ X32 @ X33))),
% 32.45/32.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 32.45/32.63  thf('76', plain,
% 32.45/32.63      (![X7 : $i, X8 : $i]:
% 32.45/32.63         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 32.45/32.63      inference('cnf', [status(esa)], [l32_xboole_1])).
% 32.45/32.63  thf('77', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 32.45/32.63          | (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 32.45/32.63      inference('sup-', [status(thm)], ['75', '76'])).
% 32.45/32.63  thf('78', plain,
% 32.45/32.63      ((((k1_xboole_0) != (k1_xboole_0))
% 32.45/32.63        | (r1_tarski @ sk_B_1 @ (k3_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 32.45/32.63      inference('sup-', [status(thm)], ['74', '77'])).
% 32.45/32.63  thf('79', plain,
% 32.45/32.63      ((r1_tarski @ sk_B_1 @ (k3_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('simplify', [status(thm)], ['78'])).
% 32.45/32.63  thf(t22_xboole_1, axiom,
% 32.45/32.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 32.45/32.63  thf('80', plain,
% 32.45/32.63      (![X18 : $i, X19 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)) = (X18))),
% 32.45/32.63      inference('cnf', [status(esa)], [t22_xboole_1])).
% 32.45/32.63  thf('81', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf(t46_xboole_1, axiom,
% 32.45/32.63    (![A:$i,B:$i]:
% 32.45/32.63     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 32.45/32.63  thf('82', plain,
% 32.45/32.63      (![X30 : $i, X31 : $i]:
% 32.45/32.63         ((k4_xboole_0 @ X30 @ (k2_xboole_0 @ X30 @ X31)) = (k1_xboole_0))),
% 32.45/32.63      inference('cnf', [status(esa)], [t46_xboole_1])).
% 32.45/32.63  thf('83', plain,
% 32.45/32.63      (![X7 : $i, X8 : $i]:
% 32.45/32.63         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 32.45/32.63      inference('cnf', [status(esa)], [l32_xboole_1])).
% 32.45/32.63  thf('84', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         (((k1_xboole_0) != (k1_xboole_0))
% 32.45/32.63          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 32.45/32.63      inference('sup-', [status(thm)], ['82', '83'])).
% 32.45/32.63  thf('85', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 32.45/32.63      inference('simplify', [status(thm)], ['84'])).
% 32.45/32.63  thf('86', plain,
% 32.45/32.63      (![X58 : $i, X60 : $i]:
% 32.45/32.63         ((m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X60)) | ~ (r1_tarski @ X58 @ X60))),
% 32.45/32.63      inference('cnf', [status(esa)], [t3_subset])).
% 32.45/32.63  thf('87', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 32.45/32.63      inference('sup-', [status(thm)], ['85', '86'])).
% 32.45/32.63  thf('88', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 32.45/32.63      inference('sup+', [status(thm)], ['81', '87'])).
% 32.45/32.63  thf('89', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['80', '88'])).
% 32.45/32.63  thf('90', plain,
% 32.45/32.63      (![X58 : $i, X59 : $i]:
% 32.45/32.63         ((r1_tarski @ X58 @ X59) | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X59)))),
% 32.45/32.63      inference('cnf', [status(esa)], [t3_subset])).
% 32.45/32.63  thf('91', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 32.45/32.63      inference('sup-', [status(thm)], ['89', '90'])).
% 32.45/32.63  thf('92', plain,
% 32.45/32.63      (![X4 : $i, X6 : $i]:
% 32.45/32.63         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 32.45/32.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 32.45/32.63  thf('93', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 32.45/32.63          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 32.45/32.63      inference('sup-', [status(thm)], ['91', '92'])).
% 32.45/32.63  thf('94', plain,
% 32.45/32.63      (((sk_B_1) = (k3_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('sup-', [status(thm)], ['79', '93'])).
% 32.45/32.63  thf(commutativity_k3_xboole_0, axiom,
% 32.45/32.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 32.45/32.63  thf('95', plain,
% 32.45/32.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 32.45/32.63  thf(t100_xboole_1, axiom,
% 32.45/32.63    (![A:$i,B:$i]:
% 32.45/32.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 32.45/32.63  thf('96', plain,
% 32.45/32.63      (![X10 : $i, X11 : $i]:
% 32.45/32.63         ((k4_xboole_0 @ X10 @ X11)
% 32.45/32.63           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 32.45/32.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 32.45/32.63  thf('97', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k4_xboole_0 @ X0 @ X1)
% 32.45/32.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 32.45/32.63      inference('sup+', [status(thm)], ['95', '96'])).
% 32.45/32.63  thf('98', plain,
% 32.45/32.63      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 32.45/32.63         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 32.45/32.63      inference('sup+', [status(thm)], ['94', '97'])).
% 32.45/32.63  thf('99', plain,
% 32.45/32.63      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 32.45/32.63         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 32.45/32.63      inference('sup-', [status(thm)], ['57', '58'])).
% 32.45/32.63  thf('100', plain,
% 32.45/32.63      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 32.45/32.63         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 32.45/32.63      inference('sup+', [status(thm)], ['98', '99'])).
% 32.45/32.63  thf('101', plain,
% 32.45/32.63      (((sk_B_1)
% 32.45/32.63         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['69', '100'])).
% 32.45/32.63  thf('102', plain,
% 32.45/32.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf(dt_k2_tops_1, axiom,
% 32.45/32.63    (![A:$i,B:$i]:
% 32.45/32.63     ( ( ( l1_pre_topc @ A ) & 
% 32.45/32.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 32.45/32.63       ( m1_subset_1 @
% 32.45/32.63         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 32.45/32.63  thf('103', plain,
% 32.45/32.63      (![X63 : $i, X64 : $i]:
% 32.45/32.63         (~ (l1_pre_topc @ X63)
% 32.45/32.63          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 32.45/32.63          | (m1_subset_1 @ (k2_tops_1 @ X63 @ X64) @ 
% 32.45/32.63             (k1_zfmisc_1 @ (u1_struct_0 @ X63))))),
% 32.45/32.63      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 32.45/32.63  thf('104', plain,
% 32.45/32.63      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 32.45/32.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 32.45/32.63        | ~ (l1_pre_topc @ sk_A))),
% 32.45/32.63      inference('sup-', [status(thm)], ['102', '103'])).
% 32.45/32.63  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf('106', plain,
% 32.45/32.63      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 32.45/32.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('demod', [status(thm)], ['104', '105'])).
% 32.45/32.63  thf('107', plain,
% 32.45/32.63      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 32.45/32.63      inference('cnf', [status(esa)], [t36_xboole_1])).
% 32.45/32.63  thf('108', plain,
% 32.45/32.63      (![X58 : $i, X60 : $i]:
% 32.45/32.63         ((m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X60)) | ~ (r1_tarski @ X58 @ X60))),
% 32.45/32.63      inference('cnf', [status(esa)], [t3_subset])).
% 32.45/32.63  thf('109', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 32.45/32.63      inference('sup-', [status(thm)], ['107', '108'])).
% 32.45/32.63  thf(redefinition_k4_subset_1, axiom,
% 32.45/32.63    (![A:$i,B:$i,C:$i]:
% 32.45/32.63     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 32.45/32.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 32.45/32.63       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 32.45/32.63  thf('110', plain,
% 32.45/32.63      (![X45 : $i, X46 : $i, X47 : $i]:
% 32.45/32.63         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 32.45/32.63          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X46))
% 32.45/32.63          | ((k4_subset_1 @ X46 @ X45 @ X47) = (k2_xboole_0 @ X45 @ X47)))),
% 32.45/32.63      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 32.45/32.63  thf('111', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.45/32.63         (((k4_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 32.45/32.63            = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))
% 32.45/32.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 32.45/32.63      inference('sup-', [status(thm)], ['109', '110'])).
% 32.45/32.63  thf('112', plain,
% 32.45/32.63      (![X0 : $i]:
% 32.45/32.63         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 32.45/32.63           (k2_tops_1 @ sk_A @ sk_B_1))
% 32.45/32.63           = (k2_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 32.45/32.63              (k2_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('sup-', [status(thm)], ['106', '111'])).
% 32.45/32.63  thf('113', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('114', plain,
% 32.45/32.63      (![X0 : $i]:
% 32.45/32.63         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 32.45/32.63           (k2_tops_1 @ sk_A @ sk_B_1))
% 32.45/32.63           = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 32.45/32.63              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 32.45/32.63      inference('demod', [status(thm)], ['112', '113'])).
% 32.45/32.63  thf('115', plain,
% 32.45/32.63      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 32.45/32.63         (k2_tops_1 @ sk_A @ sk_B_1))
% 32.45/32.63         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 32.45/32.63            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 32.45/32.63      inference('sup+', [status(thm)], ['101', '114'])).
% 32.45/32.63  thf('116', plain,
% 32.45/32.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf(t65_tops_1, axiom,
% 32.45/32.63    (![A:$i]:
% 32.45/32.63     ( ( l1_pre_topc @ A ) =>
% 32.45/32.63       ( ![B:$i]:
% 32.45/32.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 32.45/32.63           ( ( k2_pre_topc @ A @ B ) =
% 32.45/32.63             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 32.45/32.63  thf('117', plain,
% 32.45/32.63      (![X74 : $i, X75 : $i]:
% 32.45/32.63         (~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (u1_struct_0 @ X75)))
% 32.45/32.63          | ((k2_pre_topc @ X75 @ X74)
% 32.45/32.63              = (k4_subset_1 @ (u1_struct_0 @ X75) @ X74 @ 
% 32.45/32.63                 (k2_tops_1 @ X75 @ X74)))
% 32.45/32.63          | ~ (l1_pre_topc @ X75))),
% 32.45/32.63      inference('cnf', [status(esa)], [t65_tops_1])).
% 32.45/32.63  thf('118', plain,
% 32.45/32.63      ((~ (l1_pre_topc @ sk_A)
% 32.45/32.63        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 32.45/32.63            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 32.45/32.63               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 32.45/32.63      inference('sup-', [status(thm)], ['116', '117'])).
% 32.45/32.63  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf('120', plain,
% 32.45/32.63      (((k2_pre_topc @ sk_A @ sk_B_1)
% 32.45/32.63         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 32.45/32.63            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['118', '119'])).
% 32.45/32.63  thf('121', plain,
% 32.45/32.63      (((sk_B_1)
% 32.45/32.63         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['69', '100'])).
% 32.45/32.63  thf('122', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('123', plain,
% 32.45/32.63      (((k2_pre_topc @ sk_A @ sk_B_1)
% 32.45/32.63         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['115', '120', '121', '122'])).
% 32.45/32.63  thf('124', plain,
% 32.45/32.63      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 32.45/32.63         (k2_tops_1 @ sk_A @ sk_B_1)) = (k2_pre_topc @ sk_A @ sk_B_1))),
% 32.45/32.63      inference('demod', [status(thm)], ['56', '123'])).
% 32.45/32.63  thf('125', plain,
% 32.45/32.63      (![X30 : $i, X31 : $i]:
% 32.45/32.63         ((k4_xboole_0 @ X30 @ (k2_xboole_0 @ X30 @ X31)) = (k1_xboole_0))),
% 32.45/32.63      inference('cnf', [status(esa)], [t46_xboole_1])).
% 32.45/32.63  thf('126', plain,
% 32.45/32.63      (![X32 : $i, X33 : $i]:
% 32.45/32.63         ((k4_xboole_0 @ X32 @ (k3_xboole_0 @ X32 @ X33))
% 32.45/32.63           = (k4_xboole_0 @ X32 @ X33))),
% 32.45/32.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 32.45/32.63  thf('127', plain,
% 32.45/32.63      (![X22 : $i, X23 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 32.45/32.63           = (k2_xboole_0 @ X22 @ X23))),
% 32.45/32.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 32.45/32.63  thf('128', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 32.45/32.63           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 32.45/32.63      inference('sup+', [status(thm)], ['126', '127'])).
% 32.45/32.63  thf('129', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('130', plain,
% 32.45/32.63      (![X18 : $i, X19 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)) = (X18))),
% 32.45/32.63      inference('cnf', [status(esa)], [t22_xboole_1])).
% 32.45/32.63  thf('131', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 32.45/32.63           = (X1))),
% 32.45/32.63      inference('demod', [status(thm)], ['128', '129', '130'])).
% 32.45/32.63  thf('132', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 32.45/32.63           k1_xboole_0) = (X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['125', '131'])).
% 32.45/32.63  thf('133', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('134', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf(t1_boole, axiom,
% 32.45/32.63    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 32.45/32.63  thf('135', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 32.45/32.63      inference('cnf', [status(esa)], [t1_boole])).
% 32.45/32.63  thf('136', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['134', '135'])).
% 32.45/32.63  thf('137', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 32.45/32.63      inference('demod', [status(thm)], ['132', '133', '136'])).
% 32.45/32.63  thf('138', plain,
% 32.45/32.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 32.45/32.63  thf('139', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['80', '88'])).
% 32.45/32.63  thf('140', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['138', '139'])).
% 32.45/32.63  thf('141', plain,
% 32.45/32.63      (![X43 : $i, X44 : $i]:
% 32.45/32.63         (((k3_subset_1 @ X44 @ (k3_subset_1 @ X44 @ X43)) = (X43))
% 32.45/32.63          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 32.45/32.63      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 32.45/32.63  thf('142', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 32.45/32.63           = (k3_xboole_0 @ X1 @ X0))),
% 32.45/32.63      inference('sup-', [status(thm)], ['140', '141'])).
% 32.45/32.63  thf('143', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k3_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ 
% 32.45/32.63           (k3_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 32.45/32.63           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 32.45/32.63      inference('sup+', [status(thm)], ['137', '142'])).
% 32.45/32.63  thf('144', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 32.45/32.63      inference('demod', [status(thm)], ['132', '133', '136'])).
% 32.45/32.63  thf('145', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k3_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ 
% 32.45/32.63           (k3_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)) = (X0))),
% 32.45/32.63      inference('demod', [status(thm)], ['143', '144'])).
% 32.45/32.63  thf('146', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('147', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('148', plain,
% 32.45/32.63      (![X30 : $i, X31 : $i]:
% 32.45/32.63         ((k4_xboole_0 @ X30 @ (k2_xboole_0 @ X30 @ X31)) = (k1_xboole_0))),
% 32.45/32.63      inference('cnf', [status(esa)], [t46_xboole_1])).
% 32.45/32.63  thf('149', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['147', '148'])).
% 32.45/32.63  thf('150', plain,
% 32.45/32.63      (![X22 : $i, X23 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 32.45/32.63           = (k2_xboole_0 @ X22 @ X23))),
% 32.45/32.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 32.45/32.63  thf('151', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 32.45/32.63           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['149', '150'])).
% 32.45/32.63  thf('152', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('153', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['134', '135'])).
% 32.45/32.63  thf('154', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('155', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ X1 @ X0)
% 32.45/32.63           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 32.45/32.63      inference('demod', [status(thm)], ['151', '152', '153', '154'])).
% 32.45/32.63  thf('156', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ X0 @ X1)
% 32.45/32.63           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 32.45/32.63      inference('sup+', [status(thm)], ['146', '155'])).
% 32.45/32.63  thf('157', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('158', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 32.45/32.63      inference('sup+', [status(thm)], ['81', '87'])).
% 32.45/32.63  thf('159', plain,
% 32.45/32.63      (![X35 : $i, X36 : $i]:
% 32.45/32.63         (((k3_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))
% 32.45/32.63          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 32.45/32.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 32.45/32.63  thf('160', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 32.45/32.63           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 32.45/32.63      inference('sup-', [status(thm)], ['158', '159'])).
% 32.45/32.63  thf('161', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k3_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X1)
% 32.45/32.63           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 32.45/32.63      inference('sup+', [status(thm)], ['157', '160'])).
% 32.45/32.63  thf('162', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k3_subset_1 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0) @ X0)
% 32.45/32.63           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['156', '161'])).
% 32.45/32.63  thf('163', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('164', plain,
% 32.45/32.63      (![X30 : $i, X31 : $i]:
% 32.45/32.63         ((k4_xboole_0 @ X30 @ (k2_xboole_0 @ X30 @ X31)) = (k1_xboole_0))),
% 32.45/32.63      inference('cnf', [status(esa)], [t46_xboole_1])).
% 32.45/32.63  thf('165', plain,
% 32.45/32.63      (![X22 : $i, X23 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 32.45/32.63           = (k2_xboole_0 @ X22 @ X23))),
% 32.45/32.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 32.45/32.63  thf('166', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 32.45/32.63           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['164', '165'])).
% 32.45/32.63  thf('167', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('168', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['134', '135'])).
% 32.45/32.63  thf('169', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('170', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ X0 @ X1)
% 32.45/32.63           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['166', '167', '168', '169'])).
% 32.45/32.63  thf('171', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['147', '148'])).
% 32.45/32.63  thf('172', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 32.45/32.63           = (X1))),
% 32.45/32.63      inference('demod', [status(thm)], ['128', '129', '130'])).
% 32.45/32.63  thf('173', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 32.45/32.63           k1_xboole_0) = (X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['171', '172'])).
% 32.45/32.63  thf('174', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('175', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['134', '135'])).
% 32.45/32.63  thf('176', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 32.45/32.63      inference('demod', [status(thm)], ['173', '174', '175'])).
% 32.45/32.63  thf('177', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k4_xboole_0 @ X0 @ X1)
% 32.45/32.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 32.45/32.63      inference('sup+', [status(thm)], ['95', '96'])).
% 32.45/32.63  thf('178', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 32.45/32.63           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['176', '177'])).
% 32.45/32.63  thf('179', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k3_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 32.45/32.63           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 32.45/32.63      inference('demod', [status(thm)], ['162', '163', '170', '178'])).
% 32.45/32.63  thf('180', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k3_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ 
% 32.45/32.63           (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)) = (X0))),
% 32.45/32.63      inference('demod', [status(thm)], ['145', '179'])).
% 32.45/32.63  thf('181', plain,
% 32.45/32.63      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 32.45/32.63         (k5_xboole_0 @ 
% 32.45/32.63          (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 32.45/32.63           (k1_tops_1 @ sk_A @ sk_B_1)) @ 
% 32.45/32.63          (k1_tops_1 @ sk_A @ sk_B_1)))
% 32.45/32.63         = (k1_tops_1 @ sk_A @ sk_B_1))),
% 32.45/32.63      inference('sup+', [status(thm)], ['124', '180'])).
% 32.45/32.63  thf('182', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('183', plain,
% 32.45/32.63      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 32.45/32.63         (k2_tops_1 @ sk_A @ sk_B_1)) = (k2_pre_topc @ sk_A @ sk_B_1))),
% 32.45/32.63      inference('demod', [status(thm)], ['56', '123'])).
% 32.45/32.63  thf('184', plain,
% 32.45/32.63      (((k2_pre_topc @ sk_A @ sk_B_1)
% 32.45/32.63         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['115', '120', '121', '122'])).
% 32.45/32.63  thf('185', plain,
% 32.45/32.63      (((k1_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['19', '22'])).
% 32.45/32.63  thf('186', plain,
% 32.45/32.63      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 32.45/32.63      inference('cnf', [status(esa)], [t36_xboole_1])).
% 32.45/32.63  thf(t12_xboole_1, axiom,
% 32.45/32.63    (![A:$i,B:$i]:
% 32.45/32.63     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 32.45/32.63  thf('187', plain,
% 32.45/32.63      (![X12 : $i, X13 : $i]:
% 32.45/32.63         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 32.45/32.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 32.45/32.63  thf('188', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 32.45/32.63      inference('sup-', [status(thm)], ['186', '187'])).
% 32.45/32.63  thf('189', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('190', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 32.45/32.63      inference('demod', [status(thm)], ['188', '189'])).
% 32.45/32.63  thf('191', plain,
% 32.45/32.63      (((k2_xboole_0 @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 32.45/32.63      inference('sup+', [status(thm)], ['185', '190'])).
% 32.45/32.63  thf('192', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 32.45/32.63      inference('simplify', [status(thm)], ['84'])).
% 32.45/32.63  thf('193', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.45/32.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.45/32.63  thf('194', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 32.45/32.63      inference('simplify', [status(thm)], ['84'])).
% 32.45/32.63  thf(t1_xboole_1, axiom,
% 32.45/32.63    (![A:$i,B:$i,C:$i]:
% 32.45/32.63     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 32.45/32.63       ( r1_tarski @ A @ C ) ))).
% 32.45/32.63  thf('195', plain,
% 32.45/32.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 32.45/32.63         (~ (r1_tarski @ X15 @ X16)
% 32.45/32.63          | ~ (r1_tarski @ X16 @ X17)
% 32.45/32.63          | (r1_tarski @ X15 @ X17))),
% 32.45/32.63      inference('cnf', [status(esa)], [t1_xboole_1])).
% 32.45/32.63  thf('196', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.45/32.63         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 32.45/32.63      inference('sup-', [status(thm)], ['194', '195'])).
% 32.45/32.63  thf('197', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.45/32.63         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 32.45/32.63      inference('sup-', [status(thm)], ['193', '196'])).
% 32.45/32.63  thf('198', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.45/32.63         (r1_tarski @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 32.45/32.63      inference('sup-', [status(thm)], ['192', '197'])).
% 32.45/32.63  thf('199', plain,
% 32.45/32.63      (![X0 : $i]:
% 32.45/32.63         (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (k2_xboole_0 @ sk_B_1 @ X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['191', '198'])).
% 32.45/32.63  thf('200', plain,
% 32.45/32.63      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (k2_pre_topc @ sk_A @ sk_B_1))),
% 32.45/32.63      inference('sup+', [status(thm)], ['184', '199'])).
% 32.45/32.63  thf('201', plain,
% 32.45/32.63      (![X12 : $i, X13 : $i]:
% 32.45/32.63         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 32.45/32.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 32.45/32.63  thf('202', plain,
% 32.45/32.63      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 32.45/32.63         (k2_pre_topc @ sk_A @ sk_B_1)) = (k2_pre_topc @ sk_A @ sk_B_1))),
% 32.45/32.63      inference('sup-', [status(thm)], ['200', '201'])).
% 32.45/32.63  thf('203', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 32.45/32.63      inference('demod', [status(thm)], ['132', '133', '136'])).
% 32.45/32.63  thf('204', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k4_xboole_0 @ X0 @ X1)
% 32.45/32.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 32.45/32.63      inference('sup+', [status(thm)], ['95', '96'])).
% 32.45/32.63  thf('205', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 32.45/32.63           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['203', '204'])).
% 32.45/32.63  thf('206', plain,
% 32.45/32.63      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 32.45/32.63         (k1_tops_1 @ sk_A @ sk_B_1))
% 32.45/32.63         = (k5_xboole_0 @ 
% 32.45/32.63            (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 32.45/32.63             (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 32.45/32.63            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('sup+', [status(thm)], ['202', '205'])).
% 32.45/32.63  thf('207', plain,
% 32.45/32.63      (((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 32.45/32.63            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['35', '42'])).
% 32.45/32.63  thf('208', plain,
% 32.45/32.63      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 32.45/32.63         (k2_pre_topc @ sk_A @ sk_B_1)) = (k2_pre_topc @ sk_A @ sk_B_1))),
% 32.45/32.63      inference('sup-', [status(thm)], ['200', '201'])).
% 32.45/32.63  thf('209', plain,
% 32.45/32.63      (((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63         = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 32.45/32.63            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['206', '207', '208'])).
% 32.45/32.63  thf('210', plain,
% 32.45/32.63      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 32.45/32.63         (k2_tops_1 @ sk_A @ sk_B_1)) = (k1_tops_1 @ sk_A @ sk_B_1))),
% 32.45/32.63      inference('demod', [status(thm)], ['181', '182', '183', '209'])).
% 32.45/32.63  thf('211', plain,
% 32.45/32.63      (((k2_pre_topc @ sk_A @ sk_B_1)
% 32.45/32.63         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['115', '120', '121', '122'])).
% 32.45/32.63  thf('212', plain,
% 32.45/32.63      (![X0 : $i]:
% 32.45/32.63         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 32.45/32.63           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 32.45/32.63      inference('sup-', [status(thm)], ['40', '41'])).
% 32.45/32.63  thf('213', plain,
% 32.45/32.63      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 32.45/32.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 32.45/32.63      inference('split', [status(esa)], ['3'])).
% 32.45/32.63  thf('214', plain,
% 32.45/32.63      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 32.45/32.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 32.45/32.63      inference('sup+', [status(thm)], ['212', '213'])).
% 32.45/32.63  thf('215', plain,
% 32.45/32.63      (![X22 : $i, X23 : $i]:
% 32.45/32.63         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 32.45/32.63           = (k2_xboole_0 @ X22 @ X23))),
% 32.45/32.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 32.45/32.63  thf('216', plain,
% 32.45/32.63      ((((k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))
% 32.45/32.63          = (k2_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))))
% 32.45/32.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 32.45/32.63      inference('sup+', [status(thm)], ['214', '215'])).
% 32.45/32.63  thf('217', plain,
% 32.45/32.63      ((((k2_pre_topc @ sk_A @ sk_B_1)
% 32.45/32.63          = (k2_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))))
% 32.45/32.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 32.45/32.63      inference('sup+', [status(thm)], ['211', '216'])).
% 32.45/32.63  thf('218', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 32.45/32.63           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['203', '204'])).
% 32.45/32.63  thf('219', plain,
% 32.45/32.63      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 32.45/32.63          = (k5_xboole_0 @ 
% 32.45/32.63             (k2_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) @ sk_B_1)))
% 32.45/32.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 32.45/32.63      inference('sup+', [status(thm)], ['217', '218'])).
% 32.45/32.63  thf('220', plain,
% 32.45/32.63      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 32.45/32.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 32.45/32.63      inference('sup+', [status(thm)], ['212', '213'])).
% 32.45/32.63  thf('221', plain,
% 32.45/32.63      ((((k2_pre_topc @ sk_A @ sk_B_1)
% 32.45/32.63          = (k2_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))))
% 32.45/32.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 32.45/32.63      inference('sup+', [status(thm)], ['211', '216'])).
% 32.45/32.63  thf('222', plain,
% 32.45/32.63      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63          = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 32.45/32.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 32.45/32.63      inference('demod', [status(thm)], ['219', '220', '221'])).
% 32.45/32.63  thf('223', plain,
% 32.45/32.63      (((k2_pre_topc @ sk_A @ sk_B_1)
% 32.45/32.63         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['115', '120', '121', '122'])).
% 32.45/32.63  thf('224', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 32.45/32.63      inference('sup-', [status(thm)], ['85', '86'])).
% 32.45/32.63  thf('225', plain,
% 32.45/32.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('sup+', [status(thm)], ['223', '224'])).
% 32.45/32.63  thf('226', plain,
% 32.45/32.63      (![X43 : $i, X44 : $i]:
% 32.45/32.63         (((k3_subset_1 @ X44 @ (k3_subset_1 @ X44 @ X43)) = (X43))
% 32.45/32.63          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 32.45/32.63      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 32.45/32.63  thf('227', plain,
% 32.45/32.63      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 32.45/32.63         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 32.45/32.63      inference('sup-', [status(thm)], ['225', '226'])).
% 32.45/32.63  thf('228', plain,
% 32.45/32.63      (((k2_pre_topc @ sk_A @ sk_B_1)
% 32.45/32.63         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['115', '120', '121', '122'])).
% 32.45/32.63  thf('229', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 32.45/32.63           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['203', '204'])).
% 32.45/32.63  thf('230', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 32.45/32.63      inference('sup-', [status(thm)], ['85', '86'])).
% 32.45/32.63  thf('231', plain,
% 32.45/32.63      (![X35 : $i, X36 : $i]:
% 32.45/32.63         (((k3_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))
% 32.45/32.63          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 32.45/32.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 32.45/32.63  thf('232', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 32.45/32.63           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 32.45/32.63      inference('sup-', [status(thm)], ['230', '231'])).
% 32.45/32.63  thf('233', plain,
% 32.45/32.63      (![X0 : $i, X1 : $i]:
% 32.45/32.63         ((k3_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 32.45/32.63           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 32.45/32.63      inference('sup+', [status(thm)], ['229', '232'])).
% 32.45/32.63  thf('234', plain,
% 32.45/32.63      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 32.45/32.63         = (k5_xboole_0 @ 
% 32.45/32.63            (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) @ sk_B_1))),
% 32.45/32.63      inference('sup+', [status(thm)], ['228', '233'])).
% 32.45/32.63  thf('235', plain,
% 32.45/32.63      (((k2_pre_topc @ sk_A @ sk_B_1)
% 32.45/32.63         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 32.45/32.63      inference('demod', [status(thm)], ['115', '120', '121', '122'])).
% 32.45/32.63  thf('236', plain,
% 32.45/32.63      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 32.45/32.63         = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))),
% 32.45/32.63      inference('demod', [status(thm)], ['234', '235'])).
% 32.45/32.63  thf('237', plain,
% 32.45/32.63      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 32.45/32.63         (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 32.45/32.63      inference('demod', [status(thm)], ['227', '236'])).
% 32.45/32.63  thf('238', plain,
% 32.45/32.63      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 32.45/32.63          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 32.45/32.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 32.45/32.63      inference('sup+', [status(thm)], ['222', '237'])).
% 32.45/32.63  thf('239', plain,
% 32.45/32.63      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 32.45/32.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 32.45/32.63      inference('sup+', [status(thm)], ['210', '238'])).
% 32.45/32.63  thf('240', plain,
% 32.45/32.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf(fc9_tops_1, axiom,
% 32.45/32.63    (![A:$i,B:$i]:
% 32.45/32.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 32.45/32.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 32.45/32.63       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 32.45/32.63  thf('241', plain,
% 32.45/32.63      (![X65 : $i, X66 : $i]:
% 32.45/32.63         (~ (l1_pre_topc @ X65)
% 32.45/32.63          | ~ (v2_pre_topc @ X65)
% 32.45/32.63          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 32.45/32.63          | (v3_pre_topc @ (k1_tops_1 @ X65 @ X66) @ X65))),
% 32.45/32.63      inference('cnf', [status(esa)], [fc9_tops_1])).
% 32.45/32.63  thf('242', plain,
% 32.45/32.63      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 32.45/32.63        | ~ (v2_pre_topc @ sk_A)
% 32.45/32.63        | ~ (l1_pre_topc @ sk_A))),
% 32.45/32.63      inference('sup-', [status(thm)], ['240', '241'])).
% 32.45/32.63  thf('243', plain, ((v2_pre_topc @ sk_A)),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf('244', plain, ((l1_pre_topc @ sk_A)),
% 32.45/32.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.45/32.63  thf('245', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 32.45/32.63      inference('demod', [status(thm)], ['242', '243', '244'])).
% 32.45/32.63  thf('246', plain,
% 32.45/32.63      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 32.45/32.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 32.45/32.63      inference('sup+', [status(thm)], ['239', '245'])).
% 32.45/32.63  thf('247', plain,
% 32.45/32.63      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 32.45/32.63      inference('split', [status(esa)], ['0'])).
% 32.45/32.63  thf('248', plain,
% 32.45/32.63      (~
% 32.45/32.63       (((k2_tops_1 @ sk_A @ sk_B_1)
% 32.45/32.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 32.45/32.63             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 32.45/32.63       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 32.45/32.63      inference('sup-', [status(thm)], ['246', '247'])).
% 32.45/32.63  thf('249', plain, ($false),
% 32.45/32.63      inference('sat_resolution*', [status(thm)], ['1', '49', '50', '248'])).
% 32.45/32.63  
% 32.45/32.63  % SZS output end Refutation
% 32.45/32.63  
% 32.45/32.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
