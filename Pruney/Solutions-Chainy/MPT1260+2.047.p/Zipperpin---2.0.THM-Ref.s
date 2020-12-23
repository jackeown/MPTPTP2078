%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.miiqIuv4sa

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:30 EST 2020

% Result     : Theorem 4.74s
% Output     : Refutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 353 expanded)
%              Number of leaves         :   39 ( 117 expanded)
%              Depth                    :   17
%              Number of atoms          : 1656 (4208 expanded)
%              Number of equality atoms :   88 ( 190 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( v3_pre_topc @ X47 @ X48 )
      | ~ ( r1_tarski @ X47 @ X49 )
      | ( r1_tarski @ X47 @ ( k1_tops_1 @ X48 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('16',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X46 @ X45 ) @ X45 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( ( k2_tops_1 @ X44 @ X43 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X44 ) @ ( k2_pre_topc @ X44 @ X43 ) @ ( k1_tops_1 @ X44 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('44',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('45',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('47',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('48',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X24 @ ( k3_subset_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('49',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) )
    = ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('52',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('53',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('54',plain,(
    ! [X36: $i,X38: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( r1_tarski @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) )
    = ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['49','52','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('60',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X17 @ X16 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('63',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['58','65'])).

thf('67',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('69',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k4_subset_1 @ X26 @ X25 @ X27 )
        = ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('73',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k2_pre_topc @ X51 @ X50 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X51 ) @ X50 @ ( k2_tops_1 @ X51 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('74',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['71','76'])).

thf('78',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('79',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X36: $i,X38: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( r1_tarski @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('84',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['85','92'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('94',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k7_subset_1 @ X32 @ X33 @ X31 )
        = ( k9_subset_1 @ X32 @ X33 @ ( k3_subset_1 @ X32 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
        = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('97',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X24 @ ( k3_subset_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','91'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
        = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['95','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('104',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ X2 )
      = ( k4_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('107',plain,(
    ! [X36: $i,X38: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( r1_tarski @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('109',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k9_subset_1 @ X21 @ X20 @ X20 )
        = X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['102','105','110'])).

thf('112',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['77','111'])).

thf('113',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['45','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('115',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( ( k1_tops_1 @ X53 @ X52 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X53 ) @ X52 @ ( k2_tops_1 @ X53 @ X52 ) ) )
      | ~ ( l1_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('116',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['116','117','120'])).

thf('122',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['113','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('124',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X41 @ X42 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('125',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['122','128'])).

thf('130',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('131',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','41','42','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.miiqIuv4sa
% 0.12/0.35  % Computer   : n025.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 11:25:50 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 4.74/4.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.74/4.94  % Solved by: fo/fo7.sh
% 4.74/4.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.74/4.94  % done 5649 iterations in 4.476s
% 4.74/4.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.74/4.94  % SZS output start Refutation
% 4.74/4.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.74/4.94  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 4.74/4.94  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 4.74/4.94  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.74/4.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.74/4.94  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 4.74/4.94  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.74/4.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.74/4.94  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 4.74/4.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.74/4.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.74/4.94  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 4.74/4.94  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 4.74/4.94  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 4.74/4.94  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 4.74/4.94  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.74/4.94  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.74/4.94  thf(sk_A_type, type, sk_A: $i).
% 4.74/4.94  thf(t76_tops_1, conjecture,
% 4.74/4.94    (![A:$i]:
% 4.74/4.94     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.74/4.94       ( ![B:$i]:
% 4.74/4.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.74/4.94           ( ( v3_pre_topc @ B @ A ) <=>
% 4.74/4.94             ( ( k2_tops_1 @ A @ B ) =
% 4.74/4.94               ( k7_subset_1 @
% 4.74/4.94                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 4.74/4.94  thf(zf_stmt_0, negated_conjecture,
% 4.74/4.94    (~( ![A:$i]:
% 4.74/4.94        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.74/4.94          ( ![B:$i]:
% 4.74/4.94            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.74/4.94              ( ( v3_pre_topc @ B @ A ) <=>
% 4.74/4.94                ( ( k2_tops_1 @ A @ B ) =
% 4.74/4.94                  ( k7_subset_1 @
% 4.74/4.94                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 4.74/4.94    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 4.74/4.94  thf('0', plain,
% 4.74/4.94      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 4.74/4.94        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf('1', plain,
% 4.74/4.94      (~
% 4.74/4.94       (((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 4.74/4.94       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 4.74/4.94      inference('split', [status(esa)], ['0'])).
% 4.74/4.94  thf('2', plain,
% 4.74/4.94      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf('3', plain,
% 4.74/4.94      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 4.74/4.94        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf('4', plain,
% 4.74/4.94      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 4.74/4.94      inference('split', [status(esa)], ['3'])).
% 4.74/4.94  thf('5', plain,
% 4.74/4.94      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf(t56_tops_1, axiom,
% 4.74/4.94    (![A:$i]:
% 4.74/4.94     ( ( l1_pre_topc @ A ) =>
% 4.74/4.94       ( ![B:$i]:
% 4.74/4.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.74/4.94           ( ![C:$i]:
% 4.74/4.94             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.74/4.94               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 4.74/4.94                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 4.74/4.94  thf('6', plain,
% 4.74/4.94      (![X47 : $i, X48 : $i, X49 : $i]:
% 4.74/4.94         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 4.74/4.94          | ~ (v3_pre_topc @ X47 @ X48)
% 4.74/4.94          | ~ (r1_tarski @ X47 @ X49)
% 4.74/4.94          | (r1_tarski @ X47 @ (k1_tops_1 @ X48 @ X49))
% 4.74/4.94          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 4.74/4.94          | ~ (l1_pre_topc @ X48))),
% 4.74/4.94      inference('cnf', [status(esa)], [t56_tops_1])).
% 4.74/4.94  thf('7', plain,
% 4.74/4.94      (![X0 : $i]:
% 4.74/4.94         (~ (l1_pre_topc @ sk_A)
% 4.74/4.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.74/4.94          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 4.74/4.94          | ~ (r1_tarski @ sk_B_1 @ X0)
% 4.74/4.94          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 4.74/4.94      inference('sup-', [status(thm)], ['5', '6'])).
% 4.74/4.94  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf('9', plain,
% 4.74/4.94      (![X0 : $i]:
% 4.74/4.94         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.74/4.94          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 4.74/4.94          | ~ (r1_tarski @ sk_B_1 @ X0)
% 4.74/4.94          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 4.74/4.94      inference('demod', [status(thm)], ['7', '8'])).
% 4.74/4.94  thf('10', plain,
% 4.74/4.94      ((![X0 : $i]:
% 4.74/4.94          (~ (r1_tarski @ sk_B_1 @ X0)
% 4.74/4.94           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 4.74/4.94           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 4.74/4.94         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 4.74/4.94      inference('sup-', [status(thm)], ['4', '9'])).
% 4.74/4.94  thf('11', plain,
% 4.74/4.94      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 4.74/4.94         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 4.74/4.94         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 4.74/4.94      inference('sup-', [status(thm)], ['2', '10'])).
% 4.74/4.94  thf(d10_xboole_0, axiom,
% 4.74/4.94    (![A:$i,B:$i]:
% 4.74/4.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.74/4.94  thf('12', plain,
% 4.74/4.94      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 4.74/4.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.74/4.94  thf('13', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 4.74/4.94      inference('simplify', [status(thm)], ['12'])).
% 4.74/4.94  thf('14', plain,
% 4.74/4.94      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 4.74/4.94         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 4.74/4.94      inference('demod', [status(thm)], ['11', '13'])).
% 4.74/4.94  thf('15', plain,
% 4.74/4.94      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf(t44_tops_1, axiom,
% 4.74/4.94    (![A:$i]:
% 4.74/4.94     ( ( l1_pre_topc @ A ) =>
% 4.74/4.94       ( ![B:$i]:
% 4.74/4.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.74/4.94           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 4.74/4.94  thf('16', plain,
% 4.74/4.94      (![X45 : $i, X46 : $i]:
% 4.74/4.94         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 4.74/4.94          | (r1_tarski @ (k1_tops_1 @ X46 @ X45) @ X45)
% 4.74/4.94          | ~ (l1_pre_topc @ X46))),
% 4.74/4.94      inference('cnf', [status(esa)], [t44_tops_1])).
% 4.74/4.94  thf('17', plain,
% 4.74/4.94      ((~ (l1_pre_topc @ sk_A)
% 4.74/4.94        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 4.74/4.94      inference('sup-', [status(thm)], ['15', '16'])).
% 4.74/4.94  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf('19', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 4.74/4.94      inference('demod', [status(thm)], ['17', '18'])).
% 4.74/4.94  thf('20', plain,
% 4.74/4.94      (![X2 : $i, X4 : $i]:
% 4.74/4.94         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 4.74/4.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.74/4.94  thf('21', plain,
% 4.74/4.94      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 4.74/4.94        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 4.74/4.94      inference('sup-', [status(thm)], ['19', '20'])).
% 4.74/4.94  thf('22', plain,
% 4.74/4.94      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 4.74/4.94         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 4.74/4.94      inference('sup-', [status(thm)], ['14', '21'])).
% 4.74/4.94  thf('23', plain,
% 4.74/4.94      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf(l78_tops_1, axiom,
% 4.74/4.94    (![A:$i]:
% 4.74/4.94     ( ( l1_pre_topc @ A ) =>
% 4.74/4.94       ( ![B:$i]:
% 4.74/4.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.74/4.94           ( ( k2_tops_1 @ A @ B ) =
% 4.74/4.94             ( k7_subset_1 @
% 4.74/4.94               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 4.74/4.94               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 4.74/4.94  thf('24', plain,
% 4.74/4.94      (![X43 : $i, X44 : $i]:
% 4.74/4.94         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 4.74/4.94          | ((k2_tops_1 @ X44 @ X43)
% 4.74/4.94              = (k7_subset_1 @ (u1_struct_0 @ X44) @ 
% 4.74/4.94                 (k2_pre_topc @ X44 @ X43) @ (k1_tops_1 @ X44 @ X43)))
% 4.74/4.94          | ~ (l1_pre_topc @ X44))),
% 4.74/4.94      inference('cnf', [status(esa)], [l78_tops_1])).
% 4.74/4.94  thf('25', plain,
% 4.74/4.94      ((~ (l1_pre_topc @ sk_A)
% 4.74/4.94        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 4.74/4.94      inference('sup-', [status(thm)], ['23', '24'])).
% 4.74/4.94  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf('27', plain,
% 4.74/4.94      (((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 4.74/4.94      inference('demod', [status(thm)], ['25', '26'])).
% 4.74/4.94  thf('28', plain,
% 4.74/4.94      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf(dt_k2_pre_topc, axiom,
% 4.74/4.94    (![A:$i,B:$i]:
% 4.74/4.94     ( ( ( l1_pre_topc @ A ) & 
% 4.74/4.94         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.74/4.94       ( m1_subset_1 @
% 4.74/4.94         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.74/4.94  thf('29', plain,
% 4.74/4.94      (![X39 : $i, X40 : $i]:
% 4.74/4.94         (~ (l1_pre_topc @ X39)
% 4.74/4.94          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 4.74/4.94          | (m1_subset_1 @ (k2_pre_topc @ X39 @ X40) @ 
% 4.74/4.94             (k1_zfmisc_1 @ (u1_struct_0 @ X39))))),
% 4.74/4.94      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 4.74/4.94  thf('30', plain,
% 4.74/4.94      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 4.74/4.94         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.74/4.94        | ~ (l1_pre_topc @ sk_A))),
% 4.74/4.94      inference('sup-', [status(thm)], ['28', '29'])).
% 4.74/4.94  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf('32', plain,
% 4.74/4.94      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 4.74/4.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.74/4.94      inference('demod', [status(thm)], ['30', '31'])).
% 4.74/4.94  thf(redefinition_k7_subset_1, axiom,
% 4.74/4.94    (![A:$i,B:$i,C:$i]:
% 4.74/4.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.74/4.94       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 4.74/4.94  thf('33', plain,
% 4.74/4.94      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.74/4.94         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 4.74/4.94          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 4.74/4.94      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 4.74/4.94  thf('34', plain,
% 4.74/4.94      (![X0 : $i]:
% 4.74/4.94         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 4.74/4.94           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 4.74/4.94      inference('sup-', [status(thm)], ['32', '33'])).
% 4.74/4.94  thf('35', plain,
% 4.74/4.94      (((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 4.74/4.94            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 4.74/4.94      inference('demod', [status(thm)], ['27', '34'])).
% 4.74/4.94  thf('36', plain,
% 4.74/4.94      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 4.74/4.94         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 4.74/4.94      inference('sup+', [status(thm)], ['22', '35'])).
% 4.74/4.94  thf('37', plain,
% 4.74/4.94      (![X0 : $i]:
% 4.74/4.94         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 4.74/4.94           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 4.74/4.94      inference('sup-', [status(thm)], ['32', '33'])).
% 4.74/4.94  thf('38', plain,
% 4.74/4.94      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 4.74/4.94         <= (~
% 4.74/4.94             (((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 4.74/4.94      inference('split', [status(esa)], ['0'])).
% 4.74/4.94  thf('39', plain,
% 4.74/4.94      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 4.74/4.94         <= (~
% 4.74/4.94             (((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 4.74/4.94      inference('sup-', [status(thm)], ['37', '38'])).
% 4.74/4.94  thf('40', plain,
% 4.74/4.94      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 4.74/4.94         <= (~
% 4.74/4.94             (((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 4.74/4.94             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 4.74/4.94      inference('sup-', [status(thm)], ['36', '39'])).
% 4.74/4.94  thf('41', plain,
% 4.74/4.94      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 4.74/4.94       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 4.74/4.94      inference('simplify', [status(thm)], ['40'])).
% 4.74/4.94  thf('42', plain,
% 4.74/4.94      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 4.74/4.94       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 4.74/4.94      inference('split', [status(esa)], ['3'])).
% 4.74/4.94  thf('43', plain,
% 4.74/4.94      (![X0 : $i]:
% 4.74/4.94         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 4.74/4.94           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 4.74/4.94      inference('sup-', [status(thm)], ['32', '33'])).
% 4.74/4.94  thf('44', plain,
% 4.74/4.94      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 4.74/4.94         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 4.74/4.94      inference('split', [status(esa)], ['3'])).
% 4.74/4.94  thf('45', plain,
% 4.74/4.94      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 4.74/4.94         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 4.74/4.94      inference('sup+', [status(thm)], ['43', '44'])).
% 4.74/4.94  thf('46', plain,
% 4.74/4.94      (((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 4.74/4.94            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 4.74/4.94      inference('demod', [status(thm)], ['27', '34'])).
% 4.74/4.94  thf('47', plain,
% 4.74/4.94      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 4.74/4.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.74/4.94      inference('demod', [status(thm)], ['30', '31'])).
% 4.74/4.94  thf(involutiveness_k3_subset_1, axiom,
% 4.74/4.94    (![A:$i,B:$i]:
% 4.74/4.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.74/4.94       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 4.74/4.94  thf('48', plain,
% 4.74/4.94      (![X23 : $i, X24 : $i]:
% 4.74/4.94         (((k3_subset_1 @ X24 @ (k3_subset_1 @ X24 @ X23)) = (X23))
% 4.74/4.94          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 4.74/4.94      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 4.74/4.94  thf('49', plain,
% 4.74/4.94      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)))
% 4.74/4.94         = (k2_pre_topc @ sk_A @ sk_B_1))),
% 4.74/4.94      inference('sup-', [status(thm)], ['47', '48'])).
% 4.74/4.94  thf('50', plain,
% 4.74/4.94      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 4.74/4.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.74/4.94      inference('demod', [status(thm)], ['30', '31'])).
% 4.74/4.94  thf(d5_subset_1, axiom,
% 4.74/4.94    (![A:$i,B:$i]:
% 4.74/4.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.74/4.94       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 4.74/4.94  thf('51', plain,
% 4.74/4.94      (![X12 : $i, X13 : $i]:
% 4.74/4.94         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 4.74/4.94          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 4.74/4.94      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.74/4.94  thf('52', plain,
% 4.74/4.94      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1))
% 4.74/4.94         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 4.74/4.94      inference('sup-', [status(thm)], ['50', '51'])).
% 4.74/4.94  thf(t36_xboole_1, axiom,
% 4.74/4.94    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 4.74/4.94  thf('53', plain,
% 4.74/4.94      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 4.74/4.94      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.74/4.94  thf(t3_subset, axiom,
% 4.74/4.94    (![A:$i,B:$i]:
% 4.74/4.94     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.74/4.94  thf('54', plain,
% 4.74/4.94      (![X36 : $i, X38 : $i]:
% 4.74/4.94         ((m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X38)) | ~ (r1_tarski @ X36 @ X38))),
% 4.74/4.94      inference('cnf', [status(esa)], [t3_subset])).
% 4.74/4.94  thf('55', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 4.74/4.94      inference('sup-', [status(thm)], ['53', '54'])).
% 4.74/4.94  thf('56', plain,
% 4.74/4.94      (![X12 : $i, X13 : $i]:
% 4.74/4.94         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 4.74/4.94          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 4.74/4.94      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.74/4.94  thf('57', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.74/4.94           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 4.74/4.94      inference('sup-', [status(thm)], ['55', '56'])).
% 4.74/4.94  thf('58', plain,
% 4.74/4.94      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)))
% 4.74/4.94         = (k2_pre_topc @ sk_A @ sk_B_1))),
% 4.74/4.94      inference('demod', [status(thm)], ['49', '52', '57'])).
% 4.74/4.94  thf('59', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 4.74/4.94      inference('sup-', [status(thm)], ['53', '54'])).
% 4.74/4.94  thf(dt_k7_subset_1, axiom,
% 4.74/4.94    (![A:$i,B:$i,C:$i]:
% 4.74/4.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.74/4.94       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.74/4.94  thf('60', plain,
% 4.74/4.94      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.74/4.94         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 4.74/4.94          | (m1_subset_1 @ (k7_subset_1 @ X17 @ X16 @ X18) @ 
% 4.74/4.94             (k1_zfmisc_1 @ X17)))),
% 4.74/4.94      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 4.74/4.94  thf('61', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.74/4.94         (m1_subset_1 @ (k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2) @ 
% 4.74/4.94          (k1_zfmisc_1 @ X0))),
% 4.74/4.94      inference('sup-', [status(thm)], ['59', '60'])).
% 4.74/4.94  thf('62', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 4.74/4.94      inference('sup-', [status(thm)], ['53', '54'])).
% 4.74/4.94  thf('63', plain,
% 4.74/4.94      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.74/4.94         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 4.74/4.94          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 4.74/4.94      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 4.74/4.94  thf('64', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.74/4.94         ((k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 4.74/4.94           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 4.74/4.94      inference('sup-', [status(thm)], ['62', '63'])).
% 4.74/4.94  thf('65', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.74/4.94         (m1_subset_1 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2) @ 
% 4.74/4.94          (k1_zfmisc_1 @ X0))),
% 4.74/4.94      inference('demod', [status(thm)], ['61', '64'])).
% 4.74/4.94  thf('66', plain,
% 4.74/4.94      (![X0 : $i]:
% 4.74/4.94         (m1_subset_1 @ (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0) @ 
% 4.74/4.94          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.74/4.94      inference('sup+', [status(thm)], ['58', '65'])).
% 4.74/4.94  thf('67', plain,
% 4.74/4.94      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 4.74/4.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.74/4.94      inference('sup+', [status(thm)], ['46', '66'])).
% 4.74/4.94  thf('68', plain,
% 4.74/4.94      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf(redefinition_k4_subset_1, axiom,
% 4.74/4.94    (![A:$i,B:$i,C:$i]:
% 4.74/4.94     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 4.74/4.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 4.74/4.94       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 4.74/4.94  thf('69', plain,
% 4.74/4.94      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.74/4.94         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 4.74/4.94          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26))
% 4.74/4.94          | ((k4_subset_1 @ X26 @ X25 @ X27) = (k2_xboole_0 @ X25 @ X27)))),
% 4.74/4.94      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 4.74/4.94  thf('70', plain,
% 4.74/4.94      (![X0 : $i]:
% 4.74/4.94         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 4.74/4.94            = (k2_xboole_0 @ sk_B_1 @ X0))
% 4.74/4.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.74/4.94      inference('sup-', [status(thm)], ['68', '69'])).
% 4.74/4.94  thf('71', plain,
% 4.74/4.94      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 4.74/4.94         (k2_tops_1 @ sk_A @ sk_B_1))
% 4.74/4.94         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 4.74/4.94      inference('sup-', [status(thm)], ['67', '70'])).
% 4.74/4.94  thf('72', plain,
% 4.74/4.94      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf(t65_tops_1, axiom,
% 4.74/4.94    (![A:$i]:
% 4.74/4.94     ( ( l1_pre_topc @ A ) =>
% 4.74/4.94       ( ![B:$i]:
% 4.74/4.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.74/4.94           ( ( k2_pre_topc @ A @ B ) =
% 4.74/4.94             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 4.74/4.94  thf('73', plain,
% 4.74/4.94      (![X50 : $i, X51 : $i]:
% 4.74/4.94         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 4.74/4.94          | ((k2_pre_topc @ X51 @ X50)
% 4.74/4.94              = (k4_subset_1 @ (u1_struct_0 @ X51) @ X50 @ 
% 4.74/4.94                 (k2_tops_1 @ X51 @ X50)))
% 4.74/4.94          | ~ (l1_pre_topc @ X51))),
% 4.74/4.94      inference('cnf', [status(esa)], [t65_tops_1])).
% 4.74/4.94  thf('74', plain,
% 4.74/4.94      ((~ (l1_pre_topc @ sk_A)
% 4.74/4.94        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 4.74/4.94            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 4.74/4.94               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 4.74/4.94      inference('sup-', [status(thm)], ['72', '73'])).
% 4.74/4.94  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf('76', plain,
% 4.74/4.94      (((k2_pre_topc @ sk_A @ sk_B_1)
% 4.74/4.94         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 4.74/4.94            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 4.74/4.94      inference('demod', [status(thm)], ['74', '75'])).
% 4.74/4.94  thf('77', plain,
% 4.74/4.94      (((k2_pre_topc @ sk_A @ sk_B_1)
% 4.74/4.94         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 4.74/4.94      inference('sup+', [status(thm)], ['71', '76'])).
% 4.74/4.94  thf('78', plain,
% 4.74/4.94      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 4.74/4.94      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.74/4.94  thf(t44_xboole_1, axiom,
% 4.74/4.94    (![A:$i,B:$i,C:$i]:
% 4.74/4.94     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 4.74/4.94       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 4.74/4.94  thf('79', plain,
% 4.74/4.94      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.74/4.94         ((r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 4.74/4.94          | ~ (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11))),
% 4.74/4.94      inference('cnf', [status(esa)], [t44_xboole_1])).
% 4.74/4.94  thf('80', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 4.74/4.94      inference('sup-', [status(thm)], ['78', '79'])).
% 4.74/4.94  thf('81', plain,
% 4.74/4.94      (![X36 : $i, X38 : $i]:
% 4.74/4.94         ((m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X38)) | ~ (r1_tarski @ X36 @ X38))),
% 4.74/4.94      inference('cnf', [status(esa)], [t3_subset])).
% 4.74/4.94  thf('82', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.74/4.94      inference('sup-', [status(thm)], ['80', '81'])).
% 4.74/4.94  thf('83', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.74/4.94      inference('sup-', [status(thm)], ['80', '81'])).
% 4.74/4.94  thf(dt_k3_subset_1, axiom,
% 4.74/4.94    (![A:$i,B:$i]:
% 4.74/4.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.74/4.94       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.74/4.94  thf('84', plain,
% 4.74/4.94      (![X14 : $i, X15 : $i]:
% 4.74/4.94         ((m1_subset_1 @ (k3_subset_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 4.74/4.94          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 4.74/4.94      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 4.74/4.94  thf('85', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         (m1_subset_1 @ (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0) @ 
% 4.74/4.94          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.74/4.94      inference('sup-', [status(thm)], ['83', '84'])).
% 4.74/4.94  thf(commutativity_k2_xboole_0, axiom,
% 4.74/4.94    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 4.74/4.94  thf('86', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.74/4.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.74/4.94  thf('87', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.74/4.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.74/4.94  thf('88', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.74/4.94      inference('sup-', [status(thm)], ['80', '81'])).
% 4.74/4.94  thf('89', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.74/4.94      inference('sup+', [status(thm)], ['87', '88'])).
% 4.74/4.94  thf('90', plain,
% 4.74/4.94      (![X12 : $i, X13 : $i]:
% 4.74/4.94         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 4.74/4.94          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 4.74/4.94      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.74/4.94  thf('91', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 4.74/4.94           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 4.74/4.94      inference('sup-', [status(thm)], ['89', '90'])).
% 4.74/4.94  thf('92', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 4.74/4.94           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 4.74/4.94      inference('sup+', [status(thm)], ['86', '91'])).
% 4.74/4.94  thf('93', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         (m1_subset_1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0) @ 
% 4.74/4.94          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.74/4.94      inference('demod', [status(thm)], ['85', '92'])).
% 4.74/4.94  thf(t32_subset_1, axiom,
% 4.74/4.94    (![A:$i,B:$i]:
% 4.74/4.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.74/4.94       ( ![C:$i]:
% 4.74/4.94         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.74/4.94           ( ( k7_subset_1 @ A @ B @ C ) =
% 4.74/4.94             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 4.74/4.94  thf('94', plain,
% 4.74/4.94      (![X31 : $i, X32 : $i, X33 : $i]:
% 4.74/4.94         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 4.74/4.94          | ((k7_subset_1 @ X32 @ X33 @ X31)
% 4.74/4.94              = (k9_subset_1 @ X32 @ X33 @ (k3_subset_1 @ X32 @ X31)))
% 4.74/4.94          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 4.74/4.94      inference('cnf', [status(esa)], [t32_subset_1])).
% 4.74/4.94  thf('95', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.74/4.94         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 4.74/4.94          | ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 4.74/4.94              (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 4.74/4.94              = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 4.74/4.94                 (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 4.74/4.94                  (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))))),
% 4.74/4.94      inference('sup-', [status(thm)], ['93', '94'])).
% 4.74/4.94  thf('96', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.74/4.94      inference('sup-', [status(thm)], ['80', '81'])).
% 4.74/4.94  thf('97', plain,
% 4.74/4.94      (![X23 : $i, X24 : $i]:
% 4.74/4.94         (((k3_subset_1 @ X24 @ (k3_subset_1 @ X24 @ X23)) = (X23))
% 4.74/4.94          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 4.74/4.94      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 4.74/4.94  thf('98', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 4.74/4.94           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)) = (X0))),
% 4.74/4.94      inference('sup-', [status(thm)], ['96', '97'])).
% 4.74/4.94  thf('99', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 4.74/4.94           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 4.74/4.94      inference('sup+', [status(thm)], ['86', '91'])).
% 4.74/4.94  thf('100', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 4.74/4.94           (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)) = (X0))),
% 4.74/4.94      inference('demod', [status(thm)], ['98', '99'])).
% 4.74/4.94  thf('101', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.74/4.94         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 4.74/4.94          | ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 4.74/4.94              (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 4.74/4.94              = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ X0)))),
% 4.74/4.94      inference('demod', [status(thm)], ['95', '100'])).
% 4.74/4.94  thf('102', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ 
% 4.74/4.94           (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 4.74/4.94           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ X0))),
% 4.74/4.94      inference('sup-', [status(thm)], ['82', '101'])).
% 4.74/4.94  thf('103', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.74/4.94      inference('sup-', [status(thm)], ['80', '81'])).
% 4.74/4.94  thf('104', plain,
% 4.74/4.94      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.74/4.94         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 4.74/4.94          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 4.74/4.94      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 4.74/4.94  thf('105', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.74/4.94         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ X2)
% 4.74/4.94           = (k4_xboole_0 @ X0 @ X2))),
% 4.74/4.94      inference('sup-', [status(thm)], ['103', '104'])).
% 4.74/4.94  thf('106', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 4.74/4.94      inference('simplify', [status(thm)], ['12'])).
% 4.74/4.94  thf('107', plain,
% 4.74/4.94      (![X36 : $i, X38 : $i]:
% 4.74/4.94         ((m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X38)) | ~ (r1_tarski @ X36 @ X38))),
% 4.74/4.94      inference('cnf', [status(esa)], [t3_subset])).
% 4.74/4.94  thf('108', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.74/4.94      inference('sup-', [status(thm)], ['106', '107'])).
% 4.74/4.94  thf(idempotence_k9_subset_1, axiom,
% 4.74/4.94    (![A:$i,B:$i,C:$i]:
% 4.74/4.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.74/4.94       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 4.74/4.94  thf('109', plain,
% 4.74/4.94      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.74/4.94         (((k9_subset_1 @ X21 @ X20 @ X20) = (X20))
% 4.74/4.94          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 4.74/4.94      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 4.74/4.94  thf('110', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 4.74/4.94      inference('sup-', [status(thm)], ['108', '109'])).
% 4.74/4.94  thf('111', plain,
% 4.74/4.94      (![X0 : $i, X1 : $i]:
% 4.74/4.94         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 4.74/4.94           = (X0))),
% 4.74/4.94      inference('demod', [status(thm)], ['102', '105', '110'])).
% 4.74/4.94  thf('112', plain,
% 4.74/4.94      (((k4_xboole_0 @ sk_B_1 @ 
% 4.74/4.94         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 4.74/4.94      inference('sup+', [status(thm)], ['77', '111'])).
% 4.74/4.94  thf('113', plain,
% 4.74/4.94      ((((k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 4.74/4.94         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 4.74/4.94      inference('sup+', [status(thm)], ['45', '112'])).
% 4.74/4.94  thf('114', plain,
% 4.74/4.94      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf(t74_tops_1, axiom,
% 4.74/4.94    (![A:$i]:
% 4.74/4.94     ( ( l1_pre_topc @ A ) =>
% 4.74/4.94       ( ![B:$i]:
% 4.74/4.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.74/4.94           ( ( k1_tops_1 @ A @ B ) =
% 4.74/4.94             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 4.74/4.94  thf('115', plain,
% 4.74/4.94      (![X52 : $i, X53 : $i]:
% 4.74/4.94         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 4.74/4.94          | ((k1_tops_1 @ X53 @ X52)
% 4.74/4.94              = (k7_subset_1 @ (u1_struct_0 @ X53) @ X52 @ 
% 4.74/4.94                 (k2_tops_1 @ X53 @ X52)))
% 4.74/4.94          | ~ (l1_pre_topc @ X53))),
% 4.74/4.94      inference('cnf', [status(esa)], [t74_tops_1])).
% 4.74/4.94  thf('116', plain,
% 4.74/4.94      ((~ (l1_pre_topc @ sk_A)
% 4.74/4.94        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 4.74/4.94               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 4.74/4.94      inference('sup-', [status(thm)], ['114', '115'])).
% 4.74/4.94  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf('118', plain,
% 4.74/4.94      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf('119', plain,
% 4.74/4.94      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.74/4.94         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 4.74/4.94          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 4.74/4.94      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 4.74/4.94  thf('120', plain,
% 4.74/4.94      (![X0 : $i]:
% 4.74/4.94         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 4.74/4.94           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 4.74/4.94      inference('sup-', [status(thm)], ['118', '119'])).
% 4.74/4.94  thf('121', plain,
% 4.74/4.94      (((k1_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 4.74/4.94      inference('demod', [status(thm)], ['116', '117', '120'])).
% 4.74/4.94  thf('122', plain,
% 4.74/4.94      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 4.74/4.94         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 4.74/4.94      inference('sup+', [status(thm)], ['113', '121'])).
% 4.74/4.94  thf('123', plain,
% 4.74/4.94      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf(fc9_tops_1, axiom,
% 4.74/4.94    (![A:$i,B:$i]:
% 4.74/4.94     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 4.74/4.94         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.74/4.94       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 4.74/4.94  thf('124', plain,
% 4.74/4.94      (![X41 : $i, X42 : $i]:
% 4.74/4.94         (~ (l1_pre_topc @ X41)
% 4.74/4.94          | ~ (v2_pre_topc @ X41)
% 4.74/4.94          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 4.74/4.94          | (v3_pre_topc @ (k1_tops_1 @ X41 @ X42) @ X41))),
% 4.74/4.94      inference('cnf', [status(esa)], [fc9_tops_1])).
% 4.74/4.94  thf('125', plain,
% 4.74/4.94      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 4.74/4.94        | ~ (v2_pre_topc @ sk_A)
% 4.74/4.94        | ~ (l1_pre_topc @ sk_A))),
% 4.74/4.94      inference('sup-', [status(thm)], ['123', '124'])).
% 4.74/4.94  thf('126', plain, ((v2_pre_topc @ sk_A)),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 4.74/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.94  thf('128', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 4.74/4.94      inference('demod', [status(thm)], ['125', '126', '127'])).
% 4.74/4.94  thf('129', plain,
% 4.74/4.94      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 4.74/4.94         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 4.74/4.94      inference('sup+', [status(thm)], ['122', '128'])).
% 4.74/4.94  thf('130', plain,
% 4.74/4.94      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 4.74/4.94      inference('split', [status(esa)], ['0'])).
% 4.74/4.94  thf('131', plain,
% 4.74/4.94      (~
% 4.74/4.94       (((k2_tops_1 @ sk_A @ sk_B_1)
% 4.74/4.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.74/4.94             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 4.74/4.94       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 4.74/4.94      inference('sup-', [status(thm)], ['129', '130'])).
% 4.74/4.94  thf('132', plain, ($false),
% 4.74/4.94      inference('sat_resolution*', [status(thm)], ['1', '41', '42', '131'])).
% 4.74/4.94  
% 4.74/4.94  % SZS output end Refutation
% 4.74/4.94  
% 4.74/4.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
