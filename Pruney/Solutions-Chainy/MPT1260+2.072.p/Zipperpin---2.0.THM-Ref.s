%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4JY8ftZu7L

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:34 EST 2020

% Result     : Theorem 3.45s
% Output     : Refutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 458 expanded)
%              Number of leaves         :   36 ( 145 expanded)
%              Depth                    :   14
%              Number of atoms          : 1515 (6018 expanded)
%              Number of equality atoms :   84 ( 300 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( ( k1_tops_1 @ X47 @ X46 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X47 ) @ X46 @ ( k2_tops_1 @ X47 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k6_subset_1 @ X22 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k6_subset_1 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['4','5','10'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v3_pre_topc @ X41 @ X42 )
      | ~ ( r1_tarski @ X41 @ X43 )
      | ( r1_tarski @ X41 @ ( k1_tops_1 @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_tarski @ sk_B_1 @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
        = sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('33',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k2_tops_1 @ X40 @ X39 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X40 ) @ ( k2_pre_topc @ X40 @ X39 ) @ ( k1_tops_1 @ X40 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('43',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X10 @ X9 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('52',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( ( k2_pre_topc @ X45 @ X44 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 @ ( k2_tops_1 @ X45 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k6_subset_1 @ X22 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['17'])).

thf('60',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X12: $i,X13: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('62',plain,(
    ! [X12: $i,X13: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('63',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k7_subset_1 @ X26 @ X27 @ X25 )
        = ( k9_subset_1 @ X26 @ X27 @ ( k3_subset_1 @ X26 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X12: $i,X13: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('66',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('67',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('68',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k6_subset_1 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ ( k6_subset_1 @ X0 @ X2 ) )
      = ( k9_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','70'])).

thf('72',plain,(
    ! [X12: $i,X13: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('73',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k6_subset_1 @ X22 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      = ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ ( k6_subset_1 @ X0 @ X2 ) )
      = ( k9_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('77',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('79',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X15 @ X14 @ X14 )
        = X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','80'])).

thf('82',plain,
    ( ( ( k6_subset_1 @ ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['60','81'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('84',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('85',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( r1_tarski @ X33 @ ( k2_pre_topc @ X34 @ X33 ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('90',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('91',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X18 @ ( k3_subset_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('92',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('94',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k6_subset_1 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('95',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('97',plain,
    ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['92','95','96'])).

thf('98',plain,
    ( ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['83','97'])).

thf('99',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('100',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('101',plain,
    ( ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['83','97'])).

thf('102',plain,
    ( ( ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['82','98','99','100','101'])).

thf('103',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['4','5','10'])).

thf('104',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('106',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X37 @ X38 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('107',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['104','110'])).

thf('112',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('113',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','40','41','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4JY8ftZu7L
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:02:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.45/3.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.45/3.64  % Solved by: fo/fo7.sh
% 3.45/3.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.45/3.64  % done 3268 iterations in 3.182s
% 3.45/3.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.45/3.64  % SZS output start Refutation
% 3.45/3.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.45/3.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.45/3.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.45/3.64  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 3.45/3.64  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 3.45/3.64  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 3.45/3.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.45/3.64  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 3.45/3.64  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.45/3.64  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.45/3.64  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 3.45/3.64  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 3.45/3.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.45/3.64  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 3.45/3.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.45/3.64  thf(sk_A_type, type, sk_A: $i).
% 3.45/3.64  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.45/3.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.45/3.64  thf(t76_tops_1, conjecture,
% 3.45/3.64    (![A:$i]:
% 3.45/3.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.45/3.64       ( ![B:$i]:
% 3.45/3.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.45/3.64           ( ( v3_pre_topc @ B @ A ) <=>
% 3.45/3.64             ( ( k2_tops_1 @ A @ B ) =
% 3.45/3.64               ( k7_subset_1 @
% 3.45/3.64                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 3.45/3.64  thf(zf_stmt_0, negated_conjecture,
% 3.45/3.64    (~( ![A:$i]:
% 3.45/3.64        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.45/3.64          ( ![B:$i]:
% 3.45/3.64            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.45/3.64              ( ( v3_pre_topc @ B @ A ) <=>
% 3.45/3.64                ( ( k2_tops_1 @ A @ B ) =
% 3.45/3.64                  ( k7_subset_1 @
% 3.45/3.64                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 3.45/3.64    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 3.45/3.64  thf('0', plain,
% 3.45/3.64      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 3.45/3.64        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf('1', plain,
% 3.45/3.64      (~
% 3.45/3.64       (((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 3.45/3.64       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 3.45/3.64      inference('split', [status(esa)], ['0'])).
% 3.45/3.64  thf('2', plain,
% 3.45/3.64      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf(t74_tops_1, axiom,
% 3.45/3.64    (![A:$i]:
% 3.45/3.64     ( ( l1_pre_topc @ A ) =>
% 3.45/3.64       ( ![B:$i]:
% 3.45/3.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.45/3.64           ( ( k1_tops_1 @ A @ B ) =
% 3.45/3.64             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.45/3.64  thf('3', plain,
% 3.45/3.64      (![X46 : $i, X47 : $i]:
% 3.45/3.64         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 3.45/3.64          | ((k1_tops_1 @ X47 @ X46)
% 3.45/3.64              = (k7_subset_1 @ (u1_struct_0 @ X47) @ X46 @ 
% 3.45/3.64                 (k2_tops_1 @ X47 @ X46)))
% 3.45/3.64          | ~ (l1_pre_topc @ X47))),
% 3.45/3.64      inference('cnf', [status(esa)], [t74_tops_1])).
% 3.45/3.64  thf('4', plain,
% 3.45/3.64      ((~ (l1_pre_topc @ sk_A)
% 3.45/3.64        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 3.45/3.64               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 3.45/3.64      inference('sup-', [status(thm)], ['2', '3'])).
% 3.45/3.64  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf('6', plain,
% 3.45/3.64      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf(redefinition_k7_subset_1, axiom,
% 3.45/3.64    (![A:$i,B:$i,C:$i]:
% 3.45/3.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.45/3.64       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 3.45/3.64  thf('7', plain,
% 3.45/3.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.45/3.64         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 3.45/3.64          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 3.45/3.64      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.45/3.64  thf(redefinition_k6_subset_1, axiom,
% 3.45/3.64    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 3.45/3.64  thf('8', plain,
% 3.45/3.64      (![X20 : $i, X21 : $i]:
% 3.45/3.64         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 3.45/3.64      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.45/3.64  thf('9', plain,
% 3.45/3.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.45/3.64         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 3.45/3.64          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k6_subset_1 @ X22 @ X24)))),
% 3.45/3.64      inference('demod', [status(thm)], ['7', '8'])).
% 3.45/3.64  thf('10', plain,
% 3.45/3.64      (![X0 : $i]:
% 3.45/3.64         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 3.45/3.64           = (k6_subset_1 @ sk_B_1 @ X0))),
% 3.45/3.64      inference('sup-', [status(thm)], ['6', '9'])).
% 3.45/3.64  thf('11', plain,
% 3.45/3.64      (((k1_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 3.45/3.64      inference('demod', [status(thm)], ['4', '5', '10'])).
% 3.45/3.64  thf(dt_k6_subset_1, axiom,
% 3.45/3.64    (![A:$i,B:$i]:
% 3.45/3.64     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 3.45/3.64  thf('12', plain,
% 3.45/3.64      (![X12 : $i, X13 : $i]:
% 3.45/3.64         (m1_subset_1 @ (k6_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))),
% 3.45/3.64      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 3.45/3.64  thf(t3_subset, axiom,
% 3.45/3.64    (![A:$i,B:$i]:
% 3.45/3.64     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.45/3.64  thf('13', plain,
% 3.45/3.64      (![X30 : $i, X31 : $i]:
% 3.45/3.64         ((r1_tarski @ X30 @ X31) | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 3.45/3.64      inference('cnf', [status(esa)], [t3_subset])).
% 3.45/3.64  thf('14', plain,
% 3.45/3.64      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 3.45/3.64      inference('sup-', [status(thm)], ['12', '13'])).
% 3.45/3.64  thf('15', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 3.45/3.64      inference('sup+', [status(thm)], ['11', '14'])).
% 3.45/3.64  thf('16', plain,
% 3.45/3.64      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf('17', plain,
% 3.45/3.64      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 3.45/3.64        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf('18', plain,
% 3.45/3.64      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.45/3.64      inference('split', [status(esa)], ['17'])).
% 3.45/3.64  thf('19', plain,
% 3.45/3.64      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf(t56_tops_1, axiom,
% 3.45/3.64    (![A:$i]:
% 3.45/3.64     ( ( l1_pre_topc @ A ) =>
% 3.45/3.64       ( ![B:$i]:
% 3.45/3.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.45/3.64           ( ![C:$i]:
% 3.45/3.64             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.45/3.64               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 3.45/3.64                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 3.45/3.64  thf('20', plain,
% 3.45/3.64      (![X41 : $i, X42 : $i, X43 : $i]:
% 3.45/3.64         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 3.45/3.64          | ~ (v3_pre_topc @ X41 @ X42)
% 3.45/3.64          | ~ (r1_tarski @ X41 @ X43)
% 3.45/3.64          | (r1_tarski @ X41 @ (k1_tops_1 @ X42 @ X43))
% 3.45/3.64          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 3.45/3.64          | ~ (l1_pre_topc @ X42))),
% 3.45/3.64      inference('cnf', [status(esa)], [t56_tops_1])).
% 3.45/3.64  thf('21', plain,
% 3.45/3.64      (![X0 : $i]:
% 3.45/3.64         (~ (l1_pre_topc @ sk_A)
% 3.45/3.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.45/3.64          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 3.45/3.64          | ~ (r1_tarski @ sk_B_1 @ X0)
% 3.45/3.64          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 3.45/3.64      inference('sup-', [status(thm)], ['19', '20'])).
% 3.45/3.64  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf('23', plain,
% 3.45/3.64      (![X0 : $i]:
% 3.45/3.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.45/3.64          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 3.45/3.64          | ~ (r1_tarski @ sk_B_1 @ X0)
% 3.45/3.64          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 3.45/3.64      inference('demod', [status(thm)], ['21', '22'])).
% 3.45/3.64  thf('24', plain,
% 3.45/3.64      ((![X0 : $i]:
% 3.45/3.64          (~ (r1_tarski @ sk_B_1 @ X0)
% 3.45/3.64           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 3.45/3.64           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 3.45/3.64         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.45/3.64      inference('sup-', [status(thm)], ['18', '23'])).
% 3.45/3.64  thf('25', plain,
% 3.45/3.64      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 3.45/3.64         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 3.45/3.64         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.45/3.64      inference('sup-', [status(thm)], ['16', '24'])).
% 3.45/3.64  thf(d10_xboole_0, axiom,
% 3.45/3.64    (![A:$i,B:$i]:
% 3.45/3.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.45/3.64  thf('26', plain,
% 3.45/3.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.45/3.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.45/3.64  thf('27', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.45/3.64      inference('simplify', [status(thm)], ['26'])).
% 3.45/3.64  thf('28', plain,
% 3.45/3.64      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 3.45/3.64         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.45/3.64      inference('demod', [status(thm)], ['25', '27'])).
% 3.45/3.64  thf('29', plain,
% 3.45/3.64      (![X0 : $i, X2 : $i]:
% 3.45/3.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.45/3.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.45/3.64  thf('30', plain,
% 3.45/3.64      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 3.45/3.64         | ((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1))))
% 3.45/3.64         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.45/3.64      inference('sup-', [status(thm)], ['28', '29'])).
% 3.45/3.64  thf('31', plain,
% 3.45/3.64      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 3.45/3.64         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.45/3.64      inference('sup-', [status(thm)], ['15', '30'])).
% 3.45/3.64  thf('32', plain,
% 3.45/3.64      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf(l78_tops_1, axiom,
% 3.45/3.64    (![A:$i]:
% 3.45/3.64     ( ( l1_pre_topc @ A ) =>
% 3.45/3.64       ( ![B:$i]:
% 3.45/3.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.45/3.64           ( ( k2_tops_1 @ A @ B ) =
% 3.45/3.64             ( k7_subset_1 @
% 3.45/3.64               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 3.45/3.64               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.45/3.64  thf('33', plain,
% 3.45/3.64      (![X39 : $i, X40 : $i]:
% 3.45/3.64         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 3.45/3.64          | ((k2_tops_1 @ X40 @ X39)
% 3.45/3.64              = (k7_subset_1 @ (u1_struct_0 @ X40) @ 
% 3.45/3.64                 (k2_pre_topc @ X40 @ X39) @ (k1_tops_1 @ X40 @ X39)))
% 3.45/3.64          | ~ (l1_pre_topc @ X40))),
% 3.45/3.64      inference('cnf', [status(esa)], [l78_tops_1])).
% 3.45/3.64  thf('34', plain,
% 3.45/3.64      ((~ (l1_pre_topc @ sk_A)
% 3.45/3.64        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 3.45/3.64      inference('sup-', [status(thm)], ['32', '33'])).
% 3.45/3.64  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf('36', plain,
% 3.45/3.64      (((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 3.45/3.64      inference('demod', [status(thm)], ['34', '35'])).
% 3.45/3.64  thf('37', plain,
% 3.45/3.64      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 3.45/3.64         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.45/3.64      inference('sup+', [status(thm)], ['31', '36'])).
% 3.45/3.64  thf('38', plain,
% 3.45/3.64      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 3.45/3.64         <= (~
% 3.45/3.64             (((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.45/3.64      inference('split', [status(esa)], ['0'])).
% 3.45/3.64  thf('39', plain,
% 3.45/3.64      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 3.45/3.64         <= (~
% 3.45/3.64             (((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 3.45/3.64             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.45/3.64      inference('sup-', [status(thm)], ['37', '38'])).
% 3.45/3.64  thf('40', plain,
% 3.45/3.64      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 3.45/3.64       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 3.45/3.64      inference('simplify', [status(thm)], ['39'])).
% 3.45/3.64  thf('41', plain,
% 3.45/3.64      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 3.45/3.64       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 3.45/3.64      inference('split', [status(esa)], ['17'])).
% 3.45/3.64  thf('42', plain,
% 3.45/3.64      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf(dt_k2_tops_1, axiom,
% 3.45/3.64    (![A:$i,B:$i]:
% 3.45/3.64     ( ( ( l1_pre_topc @ A ) & 
% 3.45/3.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.45/3.64       ( m1_subset_1 @
% 3.45/3.64         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.45/3.64  thf('43', plain,
% 3.45/3.64      (![X35 : $i, X36 : $i]:
% 3.45/3.64         (~ (l1_pre_topc @ X35)
% 3.45/3.64          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 3.45/3.64          | (m1_subset_1 @ (k2_tops_1 @ X35 @ X36) @ 
% 3.45/3.64             (k1_zfmisc_1 @ (u1_struct_0 @ X35))))),
% 3.45/3.64      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 3.45/3.64  thf('44', plain,
% 3.45/3.64      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 3.45/3.64         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.45/3.64        | ~ (l1_pre_topc @ sk_A))),
% 3.45/3.64      inference('sup-', [status(thm)], ['42', '43'])).
% 3.45/3.64  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf('46', plain,
% 3.45/3.64      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 3.45/3.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.64      inference('demod', [status(thm)], ['44', '45'])).
% 3.45/3.64  thf('47', plain,
% 3.45/3.64      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf(dt_k4_subset_1, axiom,
% 3.45/3.64    (![A:$i,B:$i,C:$i]:
% 3.45/3.64     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.45/3.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.45/3.64       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.45/3.64  thf('48', plain,
% 3.45/3.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.45/3.64         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 3.45/3.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10))
% 3.45/3.64          | (m1_subset_1 @ (k4_subset_1 @ X10 @ X9 @ X11) @ (k1_zfmisc_1 @ X10)))),
% 3.45/3.64      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 3.45/3.64  thf('49', plain,
% 3.45/3.64      (![X0 : $i]:
% 3.45/3.64         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 3.45/3.64           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.45/3.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.45/3.64      inference('sup-', [status(thm)], ['47', '48'])).
% 3.45/3.64  thf('50', plain,
% 3.45/3.64      ((m1_subset_1 @ 
% 3.45/3.64        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 3.45/3.64         (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 3.45/3.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.64      inference('sup-', [status(thm)], ['46', '49'])).
% 3.45/3.64  thf('51', plain,
% 3.45/3.64      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf(t65_tops_1, axiom,
% 3.45/3.64    (![A:$i]:
% 3.45/3.64     ( ( l1_pre_topc @ A ) =>
% 3.45/3.64       ( ![B:$i]:
% 3.45/3.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.45/3.64           ( ( k2_pre_topc @ A @ B ) =
% 3.45/3.64             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.45/3.64  thf('52', plain,
% 3.45/3.64      (![X44 : $i, X45 : $i]:
% 3.45/3.64         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 3.45/3.64          | ((k2_pre_topc @ X45 @ X44)
% 3.45/3.64              = (k4_subset_1 @ (u1_struct_0 @ X45) @ X44 @ 
% 3.45/3.64                 (k2_tops_1 @ X45 @ X44)))
% 3.45/3.64          | ~ (l1_pre_topc @ X45))),
% 3.45/3.64      inference('cnf', [status(esa)], [t65_tops_1])).
% 3.45/3.64  thf('53', plain,
% 3.45/3.64      ((~ (l1_pre_topc @ sk_A)
% 3.45/3.64        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 3.45/3.64            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 3.45/3.64               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 3.45/3.64      inference('sup-', [status(thm)], ['51', '52'])).
% 3.45/3.64  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf('55', plain,
% 3.45/3.64      (((k2_pre_topc @ sk_A @ sk_B_1)
% 3.45/3.64         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 3.45/3.64            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 3.45/3.64      inference('demod', [status(thm)], ['53', '54'])).
% 3.45/3.64  thf('56', plain,
% 3.45/3.64      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 3.45/3.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.64      inference('demod', [status(thm)], ['50', '55'])).
% 3.45/3.64  thf('57', plain,
% 3.45/3.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.45/3.64         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 3.45/3.64          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k6_subset_1 @ X22 @ X24)))),
% 3.45/3.64      inference('demod', [status(thm)], ['7', '8'])).
% 3.45/3.64  thf('58', plain,
% 3.45/3.64      (![X0 : $i]:
% 3.45/3.64         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 3.45/3.64           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 3.45/3.64      inference('sup-', [status(thm)], ['56', '57'])).
% 3.45/3.64  thf('59', plain,
% 3.45/3.64      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 3.45/3.64         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.45/3.64      inference('split', [status(esa)], ['17'])).
% 3.45/3.64  thf('60', plain,
% 3.45/3.64      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 3.45/3.64         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.45/3.64      inference('sup+', [status(thm)], ['58', '59'])).
% 3.45/3.64  thf('61', plain,
% 3.45/3.64      (![X12 : $i, X13 : $i]:
% 3.45/3.64         (m1_subset_1 @ (k6_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))),
% 3.45/3.64      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 3.45/3.64  thf('62', plain,
% 3.45/3.64      (![X12 : $i, X13 : $i]:
% 3.45/3.64         (m1_subset_1 @ (k6_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))),
% 3.45/3.64      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 3.45/3.64  thf(t32_subset_1, axiom,
% 3.45/3.64    (![A:$i,B:$i]:
% 3.45/3.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.45/3.64       ( ![C:$i]:
% 3.45/3.64         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.45/3.64           ( ( k7_subset_1 @ A @ B @ C ) =
% 3.45/3.64             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 3.45/3.64  thf('63', plain,
% 3.45/3.64      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.45/3.64         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 3.45/3.64          | ((k7_subset_1 @ X26 @ X27 @ X25)
% 3.45/3.64              = (k9_subset_1 @ X26 @ X27 @ (k3_subset_1 @ X26 @ X25)))
% 3.45/3.64          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 3.45/3.64      inference('cnf', [status(esa)], [t32_subset_1])).
% 3.45/3.64  thf('64', plain,
% 3.45/3.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.64         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 3.45/3.64          | ((k7_subset_1 @ X0 @ X2 @ (k6_subset_1 @ X0 @ X1))
% 3.45/3.64              = (k9_subset_1 @ X0 @ X2 @ 
% 3.45/3.64                 (k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))))),
% 3.45/3.64      inference('sup-', [status(thm)], ['62', '63'])).
% 3.45/3.64  thf('65', plain,
% 3.45/3.64      (![X12 : $i, X13 : $i]:
% 3.45/3.64         (m1_subset_1 @ (k6_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))),
% 3.45/3.64      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 3.45/3.64  thf(d5_subset_1, axiom,
% 3.45/3.64    (![A:$i,B:$i]:
% 3.45/3.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.45/3.64       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 3.45/3.64  thf('66', plain,
% 3.45/3.64      (![X5 : $i, X6 : $i]:
% 3.45/3.64         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 3.45/3.64          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 3.45/3.64      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.45/3.64  thf('67', plain,
% 3.45/3.64      (![X20 : $i, X21 : $i]:
% 3.45/3.64         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 3.45/3.64      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.45/3.64  thf('68', plain,
% 3.45/3.64      (![X5 : $i, X6 : $i]:
% 3.45/3.64         (((k3_subset_1 @ X5 @ X6) = (k6_subset_1 @ X5 @ X6))
% 3.45/3.64          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 3.45/3.64      inference('demod', [status(thm)], ['66', '67'])).
% 3.45/3.64  thf('69', plain,
% 3.45/3.64      (![X0 : $i, X1 : $i]:
% 3.45/3.64         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 3.45/3.64           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 3.45/3.64      inference('sup-', [status(thm)], ['65', '68'])).
% 3.45/3.64  thf('70', plain,
% 3.45/3.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.64         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 3.45/3.64          | ((k7_subset_1 @ X0 @ X2 @ (k6_subset_1 @ X0 @ X1))
% 3.45/3.64              = (k9_subset_1 @ X0 @ X2 @ 
% 3.45/3.64                 (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))))),
% 3.45/3.64      inference('demod', [status(thm)], ['64', '69'])).
% 3.45/3.64  thf('71', plain,
% 3.45/3.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.64         ((k7_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ (k6_subset_1 @ X0 @ X2))
% 3.45/3.64           = (k9_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ 
% 3.45/3.64              (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X2))))),
% 3.45/3.64      inference('sup-', [status(thm)], ['61', '70'])).
% 3.45/3.64  thf('72', plain,
% 3.45/3.64      (![X12 : $i, X13 : $i]:
% 3.45/3.64         (m1_subset_1 @ (k6_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))),
% 3.45/3.64      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 3.45/3.64  thf('73', plain,
% 3.45/3.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.45/3.64         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 3.45/3.64          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k6_subset_1 @ X22 @ X24)))),
% 3.45/3.64      inference('demod', [status(thm)], ['7', '8'])).
% 3.45/3.64  thf('74', plain,
% 3.45/3.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.64         ((k7_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ X2)
% 3.45/3.64           = (k6_subset_1 @ (k6_subset_1 @ X0 @ X1) @ X2))),
% 3.45/3.64      inference('sup-', [status(thm)], ['72', '73'])).
% 3.45/3.64  thf('75', plain,
% 3.45/3.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.64         ((k6_subset_1 @ (k6_subset_1 @ X0 @ X1) @ (k6_subset_1 @ X0 @ X2))
% 3.45/3.64           = (k9_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ 
% 3.45/3.64              (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X2))))),
% 3.45/3.64      inference('demod', [status(thm)], ['71', '74'])).
% 3.45/3.64  thf('76', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.45/3.64      inference('simplify', [status(thm)], ['26'])).
% 3.45/3.64  thf('77', plain,
% 3.45/3.64      (![X30 : $i, X32 : $i]:
% 3.45/3.64         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 3.45/3.64      inference('cnf', [status(esa)], [t3_subset])).
% 3.45/3.64  thf('78', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.45/3.64      inference('sup-', [status(thm)], ['76', '77'])).
% 3.45/3.64  thf(idempotence_k9_subset_1, axiom,
% 3.45/3.64    (![A:$i,B:$i,C:$i]:
% 3.45/3.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.45/3.64       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 3.45/3.64  thf('79', plain,
% 3.45/3.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.45/3.64         (((k9_subset_1 @ X15 @ X14 @ X14) = (X14))
% 3.45/3.64          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 3.45/3.64      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 3.45/3.64  thf('80', plain,
% 3.45/3.64      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 3.45/3.64      inference('sup-', [status(thm)], ['78', '79'])).
% 3.45/3.64  thf('81', plain,
% 3.45/3.64      (![X0 : $i, X1 : $i]:
% 3.45/3.64         ((k6_subset_1 @ (k6_subset_1 @ X1 @ (k6_subset_1 @ X1 @ X0)) @ 
% 3.45/3.64           (k6_subset_1 @ X1 @ X0))
% 3.45/3.64           = (k6_subset_1 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 3.45/3.64      inference('sup+', [status(thm)], ['75', '80'])).
% 3.45/3.64  thf('82', plain,
% 3.45/3.64      ((((k6_subset_1 @ 
% 3.45/3.64          (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 3.45/3.64           (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 3.45/3.64          (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 3.45/3.64          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 3.45/3.64             (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))
% 3.45/3.64         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.45/3.64      inference('sup+', [status(thm)], ['60', '81'])).
% 3.45/3.64  thf('83', plain,
% 3.45/3.64      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 3.45/3.64         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.45/3.64      inference('sup+', [status(thm)], ['58', '59'])).
% 3.45/3.64  thf('84', plain,
% 3.45/3.64      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf(t48_pre_topc, axiom,
% 3.45/3.64    (![A:$i]:
% 3.45/3.64     ( ( l1_pre_topc @ A ) =>
% 3.45/3.64       ( ![B:$i]:
% 3.45/3.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.45/3.64           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 3.45/3.64  thf('85', plain,
% 3.45/3.64      (![X33 : $i, X34 : $i]:
% 3.45/3.64         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 3.45/3.64          | (r1_tarski @ X33 @ (k2_pre_topc @ X34 @ X33))
% 3.45/3.64          | ~ (l1_pre_topc @ X34))),
% 3.45/3.64      inference('cnf', [status(esa)], [t48_pre_topc])).
% 3.45/3.64  thf('86', plain,
% 3.45/3.64      ((~ (l1_pre_topc @ sk_A)
% 3.45/3.64        | (r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 3.45/3.64      inference('sup-', [status(thm)], ['84', '85'])).
% 3.45/3.64  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf('88', plain, ((r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))),
% 3.45/3.64      inference('demod', [status(thm)], ['86', '87'])).
% 3.45/3.64  thf('89', plain,
% 3.45/3.64      (![X30 : $i, X32 : $i]:
% 3.45/3.64         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 3.45/3.64      inference('cnf', [status(esa)], [t3_subset])).
% 3.45/3.64  thf('90', plain,
% 3.45/3.64      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 3.45/3.64      inference('sup-', [status(thm)], ['88', '89'])).
% 3.45/3.64  thf(involutiveness_k3_subset_1, axiom,
% 3.45/3.64    (![A:$i,B:$i]:
% 3.45/3.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.45/3.64       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 3.45/3.64  thf('91', plain,
% 3.45/3.64      (![X17 : $i, X18 : $i]:
% 3.45/3.64         (((k3_subset_1 @ X18 @ (k3_subset_1 @ X18 @ X17)) = (X17))
% 3.45/3.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 3.45/3.64      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 3.45/3.64  thf('92', plain,
% 3.45/3.64      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 3.45/3.64         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 3.45/3.64      inference('sup-', [status(thm)], ['90', '91'])).
% 3.45/3.64  thf('93', plain,
% 3.45/3.64      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 3.45/3.64      inference('sup-', [status(thm)], ['88', '89'])).
% 3.45/3.64  thf('94', plain,
% 3.45/3.64      (![X5 : $i, X6 : $i]:
% 3.45/3.64         (((k3_subset_1 @ X5 @ X6) = (k6_subset_1 @ X5 @ X6))
% 3.45/3.64          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 3.45/3.64      inference('demod', [status(thm)], ['66', '67'])).
% 3.45/3.64  thf('95', plain,
% 3.45/3.64      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 3.45/3.64         = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))),
% 3.45/3.64      inference('sup-', [status(thm)], ['93', '94'])).
% 3.45/3.64  thf('96', plain,
% 3.45/3.64      (![X0 : $i, X1 : $i]:
% 3.45/3.64         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 3.45/3.64           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 3.45/3.64      inference('sup-', [status(thm)], ['65', '68'])).
% 3.45/3.64  thf('97', plain,
% 3.45/3.64      (((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 3.45/3.64         (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 3.45/3.64      inference('demod', [status(thm)], ['92', '95', '96'])).
% 3.45/3.64  thf('98', plain,
% 3.45/3.64      ((((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 3.45/3.64          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 3.45/3.64         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.45/3.64      inference('sup+', [status(thm)], ['83', '97'])).
% 3.45/3.64  thf('99', plain,
% 3.45/3.64      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 3.45/3.64         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.45/3.64      inference('sup+', [status(thm)], ['58', '59'])).
% 3.45/3.64  thf('100', plain,
% 3.45/3.64      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 3.45/3.64         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.45/3.64      inference('sup+', [status(thm)], ['58', '59'])).
% 3.45/3.64  thf('101', plain,
% 3.45/3.64      ((((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 3.45/3.64          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 3.45/3.64         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.45/3.64      inference('sup+', [status(thm)], ['83', '97'])).
% 3.45/3.64  thf('102', plain,
% 3.45/3.64      ((((k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 3.45/3.64         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.45/3.64      inference('demod', [status(thm)], ['82', '98', '99', '100', '101'])).
% 3.45/3.64  thf('103', plain,
% 3.45/3.64      (((k1_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 3.45/3.64      inference('demod', [status(thm)], ['4', '5', '10'])).
% 3.45/3.64  thf('104', plain,
% 3.45/3.64      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 3.45/3.64         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.45/3.64      inference('sup+', [status(thm)], ['102', '103'])).
% 3.45/3.64  thf('105', plain,
% 3.45/3.64      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf(fc9_tops_1, axiom,
% 3.45/3.64    (![A:$i,B:$i]:
% 3.45/3.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 3.45/3.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.45/3.64       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 3.45/3.64  thf('106', plain,
% 3.45/3.64      (![X37 : $i, X38 : $i]:
% 3.45/3.64         (~ (l1_pre_topc @ X37)
% 3.45/3.64          | ~ (v2_pre_topc @ X37)
% 3.45/3.64          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 3.45/3.64          | (v3_pre_topc @ (k1_tops_1 @ X37 @ X38) @ X37))),
% 3.45/3.64      inference('cnf', [status(esa)], [fc9_tops_1])).
% 3.45/3.64  thf('107', plain,
% 3.45/3.64      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 3.45/3.64        | ~ (v2_pre_topc @ sk_A)
% 3.45/3.64        | ~ (l1_pre_topc @ sk_A))),
% 3.45/3.64      inference('sup-', [status(thm)], ['105', '106'])).
% 3.45/3.64  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 3.45/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.64  thf('110', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 3.45/3.64      inference('demod', [status(thm)], ['107', '108', '109'])).
% 3.45/3.64  thf('111', plain,
% 3.45/3.64      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 3.45/3.64         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.45/3.64      inference('sup+', [status(thm)], ['104', '110'])).
% 3.45/3.64  thf('112', plain,
% 3.45/3.64      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.45/3.64      inference('split', [status(esa)], ['0'])).
% 3.45/3.64  thf('113', plain,
% 3.45/3.64      (~
% 3.45/3.64       (((k2_tops_1 @ sk_A @ sk_B_1)
% 3.45/3.64          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.45/3.64             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 3.45/3.64       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 3.45/3.64      inference('sup-', [status(thm)], ['111', '112'])).
% 3.45/3.64  thf('114', plain, ($false),
% 3.45/3.64      inference('sat_resolution*', [status(thm)], ['1', '40', '41', '113'])).
% 3.45/3.64  
% 3.45/3.64  % SZS output end Refutation
% 3.45/3.64  
% 3.45/3.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
