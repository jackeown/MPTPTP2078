%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AmZdR63rrW

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:25 EST 2020

% Result     : Theorem 5.05s
% Output     : Refutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 447 expanded)
%              Number of leaves         :   37 ( 147 expanded)
%              Depth                    :   14
%              Number of atoms          : 1392 (5406 expanded)
%              Number of equality atoms :   89 ( 300 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

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
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ~ ( v3_pre_topc @ X62 @ X63 )
      | ~ ( r1_tarski @ X62 @ X64 )
      | ( r1_tarski @ X62 @ ( k1_tops_1 @ X63 @ X64 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ~ ( l1_pre_topc @ X63 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
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
    ! [X67: $i,X68: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X68 ) ) )
      | ( ( k1_tops_1 @ X68 @ X67 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X68 ) @ X67 @ ( k2_tops_1 @ X68 @ X67 ) ) )
      | ~ ( l1_pre_topc @ X68 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k7_subset_1 @ X44 @ X43 @ X45 )
        = ( k4_xboole_0 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k7_subset_1 @ X44 @ X43 @ X45 )
        = ( k6_subset_1 @ X43 @ X45 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k6_subset_1 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X30: $i,X31: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( ( k2_tops_1 @ X61 @ X60 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X61 ) @ ( k2_pre_topc @ X61 @ X60 ) @ ( k1_tops_1 @ X61 @ X60 ) ) )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('39',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( l1_pre_topc @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X54 @ X55 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k7_subset_1 @ X44 @ X43 @ X45 )
        = ( k6_subset_1 @ X43 @ X45 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','37','44'])).

thf('46',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('48',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('53',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','37','44'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('55',plain,(
    ! [X51: $i,X53: $i] :
      ( ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X53 ) )
      | ~ ( r1_tarski @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('57',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X36 @ ( k3_subset_1 @ X36 @ X35 ) )
        = X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('60',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('61',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('62',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k6_subset_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('64',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('65',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('66',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('67',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k6_subset_1 @ X17 @ X18 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','68'])).

thf('70',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['53','69'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('71',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('72',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('79',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('81',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( r1_tarski @ X56 @ ( k2_pre_topc @ X57 @ X56 ) )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('82',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X51: $i,X53: $i] :
      ( ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X53 ) )
      | ~ ( r1_tarski @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('86',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X36 @ ( k3_subset_1 @ X36 @ X35 ) )
        = X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('88',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('90',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k6_subset_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('91',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['79','92'])).

thf('94',plain,
    ( ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['76','93'])).

thf('95',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('96',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
        = ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('101',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['76','93'])).

thf('103',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['98','101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('105',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( l1_pre_topc @ X58 )
      | ~ ( v2_pre_topc @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X58 @ X59 ) @ X58 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('106',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['103','109'])).

thf('111',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('112',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','51','52','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AmZdR63rrW
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:25:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.05/5.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.05/5.25  % Solved by: fo/fo7.sh
% 5.05/5.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.05/5.25  % done 6574 iterations in 4.802s
% 5.05/5.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.05/5.25  % SZS output start Refutation
% 5.05/5.25  thf(sk_A_type, type, sk_A: $i).
% 5.05/5.25  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 5.05/5.25  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 5.05/5.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.05/5.25  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.05/5.25  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 5.05/5.25  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.05/5.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.05/5.25  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 5.05/5.25  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.05/5.25  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 5.05/5.25  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.05/5.25  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 5.05/5.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.05/5.25  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 5.05/5.25  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.05/5.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.05/5.25  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.05/5.25  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 5.05/5.25  thf(t76_tops_1, conjecture,
% 5.05/5.25    (![A:$i]:
% 5.05/5.25     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.05/5.25       ( ![B:$i]:
% 5.05/5.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.05/5.25           ( ( v3_pre_topc @ B @ A ) <=>
% 5.05/5.25             ( ( k2_tops_1 @ A @ B ) =
% 5.05/5.25               ( k7_subset_1 @
% 5.05/5.25                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 5.05/5.25  thf(zf_stmt_0, negated_conjecture,
% 5.05/5.25    (~( ![A:$i]:
% 5.05/5.25        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.05/5.25          ( ![B:$i]:
% 5.05/5.25            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.05/5.25              ( ( v3_pre_topc @ B @ A ) <=>
% 5.05/5.25                ( ( k2_tops_1 @ A @ B ) =
% 5.05/5.25                  ( k7_subset_1 @
% 5.05/5.25                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 5.05/5.25    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 5.05/5.25  thf('0', plain,
% 5.05/5.25      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.25          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.25              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 5.05/5.25        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('1', plain,
% 5.05/5.25      (~
% 5.05/5.25       (((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.25          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.25             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 5.05/5.25       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 5.05/5.25      inference('split', [status(esa)], ['0'])).
% 5.05/5.25  thf('2', plain,
% 5.05/5.25      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('3', plain,
% 5.05/5.25      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.25          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.25             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 5.05/5.25        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('4', plain,
% 5.05/5.25      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 5.05/5.25      inference('split', [status(esa)], ['3'])).
% 5.05/5.25  thf('5', plain,
% 5.05/5.25      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf(t56_tops_1, axiom,
% 5.05/5.25    (![A:$i]:
% 5.05/5.25     ( ( l1_pre_topc @ A ) =>
% 5.05/5.25       ( ![B:$i]:
% 5.05/5.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.05/5.25           ( ![C:$i]:
% 5.05/5.25             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.05/5.25               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 5.05/5.25                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 5.05/5.25  thf('6', plain,
% 5.05/5.25      (![X62 : $i, X63 : $i, X64 : $i]:
% 5.05/5.25         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 5.05/5.25          | ~ (v3_pre_topc @ X62 @ X63)
% 5.05/5.25          | ~ (r1_tarski @ X62 @ X64)
% 5.05/5.25          | (r1_tarski @ X62 @ (k1_tops_1 @ X63 @ X64))
% 5.05/5.25          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 5.05/5.25          | ~ (l1_pre_topc @ X63))),
% 5.05/5.25      inference('cnf', [status(esa)], [t56_tops_1])).
% 5.05/5.25  thf('7', plain,
% 5.05/5.25      (![X0 : $i]:
% 5.05/5.25         (~ (l1_pre_topc @ sk_A)
% 5.05/5.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.05/5.25          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 5.05/5.25          | ~ (r1_tarski @ sk_B_1 @ X0)
% 5.05/5.25          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 5.05/5.25      inference('sup-', [status(thm)], ['5', '6'])).
% 5.05/5.25  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('9', plain,
% 5.05/5.25      (![X0 : $i]:
% 5.05/5.25         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.05/5.25          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 5.05/5.25          | ~ (r1_tarski @ sk_B_1 @ X0)
% 5.05/5.25          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 5.05/5.25      inference('demod', [status(thm)], ['7', '8'])).
% 5.05/5.25  thf('10', plain,
% 5.05/5.25      ((![X0 : $i]:
% 5.05/5.25          (~ (r1_tarski @ sk_B_1 @ X0)
% 5.05/5.25           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 5.05/5.25           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 5.05/5.25         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 5.05/5.25      inference('sup-', [status(thm)], ['4', '9'])).
% 5.05/5.25  thf('11', plain,
% 5.05/5.25      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 5.05/5.25         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 5.05/5.25         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 5.05/5.25      inference('sup-', [status(thm)], ['2', '10'])).
% 5.05/5.25  thf(d10_xboole_0, axiom,
% 5.05/5.25    (![A:$i,B:$i]:
% 5.05/5.25     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.05/5.25  thf('12', plain,
% 5.05/5.25      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 5.05/5.25      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.05/5.25  thf('13', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 5.05/5.25      inference('simplify', [status(thm)], ['12'])).
% 5.05/5.25  thf('14', plain,
% 5.05/5.25      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 5.05/5.25         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 5.05/5.25      inference('demod', [status(thm)], ['11', '13'])).
% 5.05/5.25  thf('15', plain,
% 5.05/5.25      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf(t74_tops_1, axiom,
% 5.05/5.25    (![A:$i]:
% 5.05/5.25     ( ( l1_pre_topc @ A ) =>
% 5.05/5.25       ( ![B:$i]:
% 5.05/5.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.05/5.25           ( ( k1_tops_1 @ A @ B ) =
% 5.05/5.25             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 5.05/5.25  thf('16', plain,
% 5.05/5.25      (![X67 : $i, X68 : $i]:
% 5.05/5.25         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (u1_struct_0 @ X68)))
% 5.05/5.25          | ((k1_tops_1 @ X68 @ X67)
% 5.05/5.25              = (k7_subset_1 @ (u1_struct_0 @ X68) @ X67 @ 
% 5.05/5.25                 (k2_tops_1 @ X68 @ X67)))
% 5.05/5.25          | ~ (l1_pre_topc @ X68))),
% 5.05/5.25      inference('cnf', [status(esa)], [t74_tops_1])).
% 5.05/5.25  thf('17', plain,
% 5.05/5.25      ((~ (l1_pre_topc @ sk_A)
% 5.05/5.25        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.25            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 5.05/5.25               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 5.05/5.25      inference('sup-', [status(thm)], ['15', '16'])).
% 5.05/5.25  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('19', plain,
% 5.05/5.25      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf(redefinition_k7_subset_1, axiom,
% 5.05/5.25    (![A:$i,B:$i,C:$i]:
% 5.05/5.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.05/5.25       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 5.05/5.25  thf('20', plain,
% 5.05/5.25      (![X43 : $i, X44 : $i, X45 : $i]:
% 5.05/5.25         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 5.05/5.25          | ((k7_subset_1 @ X44 @ X43 @ X45) = (k4_xboole_0 @ X43 @ X45)))),
% 5.05/5.25      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 5.05/5.25  thf(redefinition_k6_subset_1, axiom,
% 5.05/5.25    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 5.05/5.25  thf('21', plain,
% 5.05/5.25      (![X41 : $i, X42 : $i]:
% 5.05/5.25         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 5.05/5.25      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 5.05/5.25  thf('22', plain,
% 5.05/5.25      (![X43 : $i, X44 : $i, X45 : $i]:
% 5.05/5.25         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 5.05/5.25          | ((k7_subset_1 @ X44 @ X43 @ X45) = (k6_subset_1 @ X43 @ X45)))),
% 5.05/5.25      inference('demod', [status(thm)], ['20', '21'])).
% 5.05/5.25  thf('23', plain,
% 5.05/5.25      (![X0 : $i]:
% 5.05/5.25         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 5.05/5.25           = (k6_subset_1 @ sk_B_1 @ X0))),
% 5.05/5.25      inference('sup-', [status(thm)], ['19', '22'])).
% 5.05/5.25  thf('24', plain,
% 5.05/5.25      (((k1_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.25         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('demod', [status(thm)], ['17', '18', '23'])).
% 5.05/5.25  thf(dt_k6_subset_1, axiom,
% 5.05/5.25    (![A:$i,B:$i]:
% 5.05/5.25     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 5.05/5.25  thf('25', plain,
% 5.05/5.25      (![X30 : $i, X31 : $i]:
% 5.05/5.25         (m1_subset_1 @ (k6_subset_1 @ X30 @ X31) @ (k1_zfmisc_1 @ X30))),
% 5.05/5.25      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 5.05/5.25  thf(t3_subset, axiom,
% 5.05/5.25    (![A:$i,B:$i]:
% 5.05/5.25     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.05/5.25  thf('26', plain,
% 5.05/5.25      (![X51 : $i, X52 : $i]:
% 5.05/5.25         ((r1_tarski @ X51 @ X52) | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X52)))),
% 5.05/5.25      inference('cnf', [status(esa)], [t3_subset])).
% 5.05/5.25  thf('27', plain,
% 5.05/5.25      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 5.05/5.25      inference('sup-', [status(thm)], ['25', '26'])).
% 5.05/5.25  thf('28', plain,
% 5.05/5.25      (![X6 : $i, X8 : $i]:
% 5.05/5.25         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 5.05/5.25      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.05/5.25  thf('29', plain,
% 5.05/5.25      (![X0 : $i, X1 : $i]:
% 5.05/5.25         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 5.05/5.25          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 5.05/5.25      inference('sup-', [status(thm)], ['27', '28'])).
% 5.05/5.25  thf('30', plain,
% 5.05/5.25      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 5.05/5.25        | ((sk_B_1) = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 5.05/5.25      inference('sup-', [status(thm)], ['24', '29'])).
% 5.05/5.25  thf('31', plain,
% 5.05/5.25      (((k1_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.25         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('demod', [status(thm)], ['17', '18', '23'])).
% 5.05/5.25  thf('32', plain,
% 5.05/5.25      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 5.05/5.25        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('demod', [status(thm)], ['30', '31'])).
% 5.05/5.25  thf('33', plain,
% 5.05/5.25      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 5.05/5.25         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 5.05/5.25      inference('sup-', [status(thm)], ['14', '32'])).
% 5.05/5.25  thf('34', plain,
% 5.05/5.25      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf(l78_tops_1, axiom,
% 5.05/5.25    (![A:$i]:
% 5.05/5.25     ( ( l1_pre_topc @ A ) =>
% 5.05/5.25       ( ![B:$i]:
% 5.05/5.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.05/5.25           ( ( k2_tops_1 @ A @ B ) =
% 5.05/5.25             ( k7_subset_1 @
% 5.05/5.25               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 5.05/5.25               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 5.05/5.25  thf('35', plain,
% 5.05/5.25      (![X60 : $i, X61 : $i]:
% 5.05/5.25         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 5.05/5.25          | ((k2_tops_1 @ X61 @ X60)
% 5.05/5.25              = (k7_subset_1 @ (u1_struct_0 @ X61) @ 
% 5.05/5.25                 (k2_pre_topc @ X61 @ X60) @ (k1_tops_1 @ X61 @ X60)))
% 5.05/5.25          | ~ (l1_pre_topc @ X61))),
% 5.05/5.25      inference('cnf', [status(esa)], [l78_tops_1])).
% 5.05/5.25  thf('36', plain,
% 5.05/5.25      ((~ (l1_pre_topc @ sk_A)
% 5.05/5.25        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.25            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.25               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 5.05/5.25      inference('sup-', [status(thm)], ['34', '35'])).
% 5.05/5.25  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('38', plain,
% 5.05/5.25      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf(dt_k2_pre_topc, axiom,
% 5.05/5.25    (![A:$i,B:$i]:
% 5.05/5.25     ( ( ( l1_pre_topc @ A ) & 
% 5.05/5.25         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.05/5.25       ( m1_subset_1 @
% 5.05/5.25         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.05/5.25  thf('39', plain,
% 5.05/5.25      (![X54 : $i, X55 : $i]:
% 5.05/5.25         (~ (l1_pre_topc @ X54)
% 5.05/5.25          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 5.05/5.25          | (m1_subset_1 @ (k2_pre_topc @ X54 @ X55) @ 
% 5.05/5.25             (k1_zfmisc_1 @ (u1_struct_0 @ X54))))),
% 5.05/5.25      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 5.05/5.25  thf('40', plain,
% 5.05/5.25      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 5.05/5.25         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.05/5.25        | ~ (l1_pre_topc @ sk_A))),
% 5.05/5.25      inference('sup-', [status(thm)], ['38', '39'])).
% 5.05/5.25  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('42', plain,
% 5.05/5.25      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 5.05/5.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.05/5.25      inference('demod', [status(thm)], ['40', '41'])).
% 5.05/5.25  thf('43', plain,
% 5.05/5.25      (![X43 : $i, X44 : $i, X45 : $i]:
% 5.05/5.25         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 5.05/5.25          | ((k7_subset_1 @ X44 @ X43 @ X45) = (k6_subset_1 @ X43 @ X45)))),
% 5.05/5.25      inference('demod', [status(thm)], ['20', '21'])).
% 5.05/5.25  thf('44', plain,
% 5.05/5.25      (![X0 : $i]:
% 5.05/5.25         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.25           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 5.05/5.25           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 5.05/5.25      inference('sup-', [status(thm)], ['42', '43'])).
% 5.05/5.25  thf('45', plain,
% 5.05/5.25      (((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.25         = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 5.05/5.25            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('demod', [status(thm)], ['36', '37', '44'])).
% 5.05/5.25  thf('46', plain,
% 5.05/5.25      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.25          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 5.05/5.26         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 5.05/5.26      inference('sup+', [status(thm)], ['33', '45'])).
% 5.05/5.26  thf('47', plain,
% 5.05/5.26      (![X0 : $i]:
% 5.05/5.26         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 5.05/5.26           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 5.05/5.26      inference('sup-', [status(thm)], ['42', '43'])).
% 5.05/5.26  thf('48', plain,
% 5.05/5.26      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 5.05/5.26         <= (~
% 5.05/5.26             (((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 5.05/5.26      inference('split', [status(esa)], ['0'])).
% 5.05/5.26  thf('49', plain,
% 5.05/5.26      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26          != (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 5.05/5.26         <= (~
% 5.05/5.26             (((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 5.05/5.26      inference('sup-', [status(thm)], ['47', '48'])).
% 5.05/5.26  thf('50', plain,
% 5.05/5.26      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 5.05/5.26         <= (~
% 5.05/5.26             (((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 5.05/5.26             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 5.05/5.26      inference('sup-', [status(thm)], ['46', '49'])).
% 5.05/5.26  thf('51', plain,
% 5.05/5.26      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 5.05/5.26       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 5.05/5.26      inference('simplify', [status(thm)], ['50'])).
% 5.05/5.26  thf('52', plain,
% 5.05/5.26      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 5.05/5.26       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 5.05/5.26      inference('split', [status(esa)], ['3'])).
% 5.05/5.26  thf('53', plain,
% 5.05/5.26      (((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26         = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 5.05/5.26            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 5.05/5.26      inference('demod', [status(thm)], ['36', '37', '44'])).
% 5.05/5.26  thf(t17_xboole_1, axiom,
% 5.05/5.26    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 5.05/5.26  thf('54', plain,
% 5.05/5.26      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 5.05/5.26      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.05/5.26  thf('55', plain,
% 5.05/5.26      (![X51 : $i, X53 : $i]:
% 5.05/5.26         ((m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X53)) | ~ (r1_tarski @ X51 @ X53))),
% 5.05/5.26      inference('cnf', [status(esa)], [t3_subset])).
% 5.05/5.26  thf('56', plain,
% 5.05/5.26      (![X0 : $i, X1 : $i]:
% 5.05/5.26         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 5.05/5.26      inference('sup-', [status(thm)], ['54', '55'])).
% 5.05/5.26  thf(involutiveness_k3_subset_1, axiom,
% 5.05/5.26    (![A:$i,B:$i]:
% 5.05/5.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.05/5.26       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 5.05/5.26  thf('57', plain,
% 5.05/5.26      (![X35 : $i, X36 : $i]:
% 5.05/5.26         (((k3_subset_1 @ X36 @ (k3_subset_1 @ X36 @ X35)) = (X35))
% 5.05/5.26          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 5.05/5.26      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 5.05/5.26  thf('58', plain,
% 5.05/5.26      (![X0 : $i, X1 : $i]:
% 5.05/5.26         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 5.05/5.26           = (k3_xboole_0 @ X0 @ X1))),
% 5.05/5.26      inference('sup-', [status(thm)], ['56', '57'])).
% 5.05/5.26  thf('59', plain,
% 5.05/5.26      (![X0 : $i, X1 : $i]:
% 5.05/5.26         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 5.05/5.26      inference('sup-', [status(thm)], ['54', '55'])).
% 5.05/5.26  thf(d5_subset_1, axiom,
% 5.05/5.26    (![A:$i,B:$i]:
% 5.05/5.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.05/5.26       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 5.05/5.26  thf('60', plain,
% 5.05/5.26      (![X26 : $i, X27 : $i]:
% 5.05/5.26         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 5.05/5.26          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 5.05/5.26      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.05/5.26  thf('61', plain,
% 5.05/5.26      (![X41 : $i, X42 : $i]:
% 5.05/5.26         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 5.05/5.26      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 5.05/5.26  thf('62', plain,
% 5.05/5.26      (![X26 : $i, X27 : $i]:
% 5.05/5.26         (((k3_subset_1 @ X26 @ X27) = (k6_subset_1 @ X26 @ X27))
% 5.05/5.26          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 5.05/5.26      inference('demod', [status(thm)], ['60', '61'])).
% 5.05/5.26  thf('63', plain,
% 5.05/5.26      (![X0 : $i, X1 : $i]:
% 5.05/5.26         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 5.05/5.26           = (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 5.05/5.26      inference('sup-', [status(thm)], ['59', '62'])).
% 5.05/5.26  thf(t47_xboole_1, axiom,
% 5.05/5.26    (![A:$i,B:$i]:
% 5.05/5.26     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 5.05/5.26  thf('64', plain,
% 5.05/5.26      (![X17 : $i, X18 : $i]:
% 5.05/5.26         ((k4_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 5.05/5.26           = (k4_xboole_0 @ X17 @ X18))),
% 5.05/5.26      inference('cnf', [status(esa)], [t47_xboole_1])).
% 5.05/5.26  thf('65', plain,
% 5.05/5.26      (![X41 : $i, X42 : $i]:
% 5.05/5.26         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 5.05/5.26      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 5.05/5.26  thf('66', plain,
% 5.05/5.26      (![X41 : $i, X42 : $i]:
% 5.05/5.26         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 5.05/5.26      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 5.05/5.26  thf('67', plain,
% 5.05/5.26      (![X17 : $i, X18 : $i]:
% 5.05/5.26         ((k6_subset_1 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 5.05/5.26           = (k6_subset_1 @ X17 @ X18))),
% 5.05/5.26      inference('demod', [status(thm)], ['64', '65', '66'])).
% 5.05/5.26  thf('68', plain,
% 5.05/5.26      (![X0 : $i, X1 : $i]:
% 5.05/5.26         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 5.05/5.26           = (k6_subset_1 @ X0 @ X1))),
% 5.05/5.26      inference('demod', [status(thm)], ['63', '67'])).
% 5.05/5.26  thf('69', plain,
% 5.05/5.26      (![X0 : $i, X1 : $i]:
% 5.05/5.26         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 5.05/5.26           = (k3_xboole_0 @ X0 @ X1))),
% 5.05/5.26      inference('demod', [status(thm)], ['58', '68'])).
% 5.05/5.26  thf('70', plain,
% 5.05/5.26      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 5.05/5.26         (k2_tops_1 @ sk_A @ sk_B_1))
% 5.05/5.26         = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 5.05/5.26            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 5.05/5.26      inference('sup+', [status(thm)], ['53', '69'])).
% 5.05/5.26  thf(commutativity_k2_tarski, axiom,
% 5.05/5.26    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 5.05/5.26  thf('71', plain,
% 5.05/5.26      (![X22 : $i, X23 : $i]:
% 5.05/5.26         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 5.05/5.26      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.05/5.26  thf(t12_setfam_1, axiom,
% 5.05/5.26    (![A:$i,B:$i]:
% 5.05/5.26     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.05/5.26  thf('72', plain,
% 5.05/5.26      (![X49 : $i, X50 : $i]:
% 5.05/5.26         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 5.05/5.26      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.05/5.26  thf('73', plain,
% 5.05/5.26      (![X0 : $i, X1 : $i]:
% 5.05/5.26         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 5.05/5.26      inference('sup+', [status(thm)], ['71', '72'])).
% 5.05/5.26  thf('74', plain,
% 5.05/5.26      (![X49 : $i, X50 : $i]:
% 5.05/5.26         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 5.05/5.26      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.05/5.26  thf('75', plain,
% 5.05/5.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.05/5.26      inference('sup+', [status(thm)], ['73', '74'])).
% 5.05/5.26  thf('76', plain,
% 5.05/5.26      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 5.05/5.26         (k2_tops_1 @ sk_A @ sk_B_1))
% 5.05/5.26         = (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 5.05/5.26            (k2_pre_topc @ sk_A @ sk_B_1)))),
% 5.05/5.26      inference('demod', [status(thm)], ['70', '75'])).
% 5.05/5.26  thf('77', plain,
% 5.05/5.26      (![X0 : $i]:
% 5.05/5.26         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 5.05/5.26           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 5.05/5.26      inference('sup-', [status(thm)], ['42', '43'])).
% 5.05/5.26  thf('78', plain,
% 5.05/5.26      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 5.05/5.26         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 5.05/5.26      inference('split', [status(esa)], ['3'])).
% 5.05/5.26  thf('79', plain,
% 5.05/5.26      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 5.05/5.26         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 5.05/5.26      inference('sup+', [status(thm)], ['77', '78'])).
% 5.05/5.26  thf('80', plain,
% 5.05/5.26      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.05/5.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.26  thf(t48_pre_topc, axiom,
% 5.05/5.26    (![A:$i]:
% 5.05/5.26     ( ( l1_pre_topc @ A ) =>
% 5.05/5.26       ( ![B:$i]:
% 5.05/5.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.05/5.26           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 5.05/5.26  thf('81', plain,
% 5.05/5.26      (![X56 : $i, X57 : $i]:
% 5.05/5.26         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 5.05/5.26          | (r1_tarski @ X56 @ (k2_pre_topc @ X57 @ X56))
% 5.05/5.26          | ~ (l1_pre_topc @ X57))),
% 5.05/5.26      inference('cnf', [status(esa)], [t48_pre_topc])).
% 5.05/5.26  thf('82', plain,
% 5.05/5.26      ((~ (l1_pre_topc @ sk_A)
% 5.05/5.26        | (r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 5.05/5.26      inference('sup-', [status(thm)], ['80', '81'])).
% 5.05/5.26  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 5.05/5.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.26  thf('84', plain, ((r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))),
% 5.05/5.26      inference('demod', [status(thm)], ['82', '83'])).
% 5.05/5.26  thf('85', plain,
% 5.05/5.26      (![X51 : $i, X53 : $i]:
% 5.05/5.26         ((m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X53)) | ~ (r1_tarski @ X51 @ X53))),
% 5.05/5.26      inference('cnf', [status(esa)], [t3_subset])).
% 5.05/5.26  thf('86', plain,
% 5.05/5.26      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 5.05/5.26      inference('sup-', [status(thm)], ['84', '85'])).
% 5.05/5.26  thf('87', plain,
% 5.05/5.26      (![X35 : $i, X36 : $i]:
% 5.05/5.26         (((k3_subset_1 @ X36 @ (k3_subset_1 @ X36 @ X35)) = (X35))
% 5.05/5.26          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 5.05/5.26      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 5.05/5.26  thf('88', plain,
% 5.05/5.26      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 5.05/5.26         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 5.05/5.26      inference('sup-', [status(thm)], ['86', '87'])).
% 5.05/5.26  thf('89', plain,
% 5.05/5.26      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 5.05/5.26      inference('sup-', [status(thm)], ['84', '85'])).
% 5.05/5.26  thf('90', plain,
% 5.05/5.26      (![X26 : $i, X27 : $i]:
% 5.05/5.26         (((k3_subset_1 @ X26 @ X27) = (k6_subset_1 @ X26 @ X27))
% 5.05/5.26          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 5.05/5.26      inference('demod', [status(thm)], ['60', '61'])).
% 5.05/5.26  thf('91', plain,
% 5.05/5.26      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 5.05/5.26         = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))),
% 5.05/5.26      inference('sup-', [status(thm)], ['89', '90'])).
% 5.05/5.26  thf('92', plain,
% 5.05/5.26      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 5.05/5.26         (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 5.05/5.26      inference('demod', [status(thm)], ['88', '91'])).
% 5.05/5.26  thf('93', plain,
% 5.05/5.26      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 5.05/5.26          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 5.05/5.26         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 5.05/5.26      inference('sup+', [status(thm)], ['79', '92'])).
% 5.05/5.26  thf('94', plain,
% 5.05/5.26      ((((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 5.05/5.26          (k2_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1)))
% 5.05/5.26         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 5.05/5.26      inference('sup+', [status(thm)], ['76', '93'])).
% 5.05/5.26  thf('95', plain,
% 5.05/5.26      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 5.05/5.26      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.05/5.26  thf('96', plain,
% 5.05/5.26      (![X6 : $i, X8 : $i]:
% 5.05/5.26         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 5.05/5.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.05/5.26  thf('97', plain,
% 5.05/5.26      (![X0 : $i, X1 : $i]:
% 5.05/5.26         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 5.05/5.26          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 5.05/5.26      inference('sup-', [status(thm)], ['95', '96'])).
% 5.05/5.26  thf('98', plain,
% 5.05/5.26      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 5.05/5.26         | ((k1_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26             = (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 5.05/5.26                (k2_pre_topc @ sk_A @ sk_B_1)))))
% 5.05/5.26         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 5.05/5.26      inference('sup-', [status(thm)], ['94', '97'])).
% 5.05/5.26  thf('99', plain,
% 5.05/5.26      (((k1_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 5.05/5.26      inference('demod', [status(thm)], ['17', '18', '23'])).
% 5.05/5.26  thf('100', plain,
% 5.05/5.26      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 5.05/5.26      inference('sup-', [status(thm)], ['25', '26'])).
% 5.05/5.26  thf('101', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 5.05/5.26      inference('sup+', [status(thm)], ['99', '100'])).
% 5.05/5.26  thf('102', plain,
% 5.05/5.26      ((((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 5.05/5.26          (k2_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1)))
% 5.05/5.26         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 5.05/5.26      inference('sup+', [status(thm)], ['76', '93'])).
% 5.05/5.26  thf('103', plain,
% 5.05/5.26      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 5.05/5.26         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 5.05/5.26      inference('demod', [status(thm)], ['98', '101', '102'])).
% 5.05/5.26  thf('104', plain,
% 5.05/5.26      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.05/5.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.26  thf(fc9_tops_1, axiom,
% 5.05/5.26    (![A:$i,B:$i]:
% 5.05/5.26     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 5.05/5.26         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.05/5.26       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 5.05/5.26  thf('105', plain,
% 5.05/5.26      (![X58 : $i, X59 : $i]:
% 5.05/5.26         (~ (l1_pre_topc @ X58)
% 5.05/5.26          | ~ (v2_pre_topc @ X58)
% 5.05/5.26          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 5.05/5.26          | (v3_pre_topc @ (k1_tops_1 @ X58 @ X59) @ X58))),
% 5.05/5.26      inference('cnf', [status(esa)], [fc9_tops_1])).
% 5.05/5.26  thf('106', plain,
% 5.05/5.26      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 5.05/5.26        | ~ (v2_pre_topc @ sk_A)
% 5.05/5.26        | ~ (l1_pre_topc @ sk_A))),
% 5.05/5.26      inference('sup-', [status(thm)], ['104', '105'])).
% 5.05/5.26  thf('107', plain, ((v2_pre_topc @ sk_A)),
% 5.05/5.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.26  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 5.05/5.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.26  thf('109', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 5.05/5.26      inference('demod', [status(thm)], ['106', '107', '108'])).
% 5.05/5.26  thf('110', plain,
% 5.05/5.26      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 5.05/5.26         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 5.05/5.26      inference('sup+', [status(thm)], ['103', '109'])).
% 5.05/5.26  thf('111', plain,
% 5.05/5.26      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 5.05/5.26      inference('split', [status(esa)], ['0'])).
% 5.05/5.26  thf('112', plain,
% 5.05/5.26      (~
% 5.05/5.26       (((k2_tops_1 @ sk_A @ sk_B_1)
% 5.05/5.26          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.05/5.26             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 5.05/5.26       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 5.05/5.26      inference('sup-', [status(thm)], ['110', '111'])).
% 5.05/5.26  thf('113', plain, ($false),
% 5.05/5.26      inference('sat_resolution*', [status(thm)], ['1', '51', '52', '112'])).
% 5.05/5.26  
% 5.05/5.26  % SZS output end Refutation
% 5.05/5.26  
% 5.05/5.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
