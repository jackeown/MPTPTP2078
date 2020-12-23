%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MxDWT4Qypl

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:33 EST 2020

% Result     : Theorem 4.32s
% Output     : Refutation 4.41s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 800 expanded)
%              Number of leaves         :   33 ( 248 expanded)
%              Depth                    :   21
%              Number of atoms          : 1680 (8752 expanded)
%              Number of equality atoms :  104 ( 479 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v3_pre_topc @ X43 @ X44 )
      | ~ ( r1_tarski @ X43 @ X45 )
      | ( r1_tarski @ X43 @ ( k1_tops_1 @ X44 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('16',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X42 @ X41 ) @ X41 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k2_tops_1 @ X40 @ X39 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X40 ) @ ( k2_pre_topc @ X40 @ X39 ) @ ( k1_tops_1 @ X40 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['22','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('44',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( ( k1_tops_1 @ X47 @ X46 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X47 ) @ X46 @ ( k2_tops_1 @ X47 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('56',plain,(
    ! [X27: $i,X29: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('58',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X13 @ X12 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('61',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('64',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X19 @ ( k3_subset_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('67',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','77'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('79',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','80'])).

thf('82',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('83',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('84',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('86',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','76'])).

thf('88',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('90',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('92',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( r1_tarski @ X35 @ ( k2_pre_topc @ X36 @ X35 ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X27: $i,X29: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X13 @ X12 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('101',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X19 @ ( k3_subset_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['99','102'])).

thf('107',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['105','108','109'])).

thf('111',plain,
    ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['90','110'])).

thf('112',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('113',plain,
    ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('115',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('116',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('118',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('119',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('121',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('123',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X19 @ ( k3_subset_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('124',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('126',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('127',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('129',plain,
    ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['124','127','128'])).

thf('130',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['121','129'])).

thf('131',plain,
    ( ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['116','130'])).

thf('132',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['113','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('134',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X37 @ X38 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('135',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['132','138'])).

thf('140',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('141',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','41','42','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MxDWT4Qypl
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.32/4.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.32/4.58  % Solved by: fo/fo7.sh
% 4.32/4.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.32/4.58  % done 10792 iterations in 4.127s
% 4.32/4.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.32/4.58  % SZS output start Refutation
% 4.32/4.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.32/4.58  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 4.32/4.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.32/4.58  thf(sk_A_type, type, sk_A: $i).
% 4.32/4.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 4.32/4.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 4.32/4.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.32/4.58  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 4.32/4.58  thf(sk_B_type, type, sk_B: $i).
% 4.32/4.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.32/4.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.32/4.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.32/4.58  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 4.32/4.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.32/4.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 4.32/4.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.32/4.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.32/4.58  thf(t76_tops_1, conjecture,
% 4.32/4.58    (![A:$i]:
% 4.32/4.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.32/4.58       ( ![B:$i]:
% 4.32/4.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.32/4.58           ( ( v3_pre_topc @ B @ A ) <=>
% 4.32/4.58             ( ( k2_tops_1 @ A @ B ) =
% 4.32/4.58               ( k7_subset_1 @
% 4.32/4.58                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 4.32/4.58  thf(zf_stmt_0, negated_conjecture,
% 4.32/4.58    (~( ![A:$i]:
% 4.32/4.58        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.32/4.58          ( ![B:$i]:
% 4.32/4.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.32/4.58              ( ( v3_pre_topc @ B @ A ) <=>
% 4.32/4.58                ( ( k2_tops_1 @ A @ B ) =
% 4.32/4.58                  ( k7_subset_1 @
% 4.32/4.58                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 4.32/4.58    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 4.32/4.58  thf('0', plain,
% 4.32/4.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 4.32/4.58          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.32/4.58              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 4.32/4.58        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 4.32/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.58  thf('1', plain,
% 4.32/4.58      (~
% 4.32/4.58       (((k2_tops_1 @ sk_A @ sk_B)
% 4.32/4.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.32/4.58             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 4.32/4.58       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 4.32/4.58      inference('split', [status(esa)], ['0'])).
% 4.32/4.58  thf('2', plain,
% 4.32/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.32/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.58  thf('3', plain,
% 4.32/4.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 4.32/4.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.32/4.58             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 4.32/4.58        | (v3_pre_topc @ sk_B @ sk_A))),
% 4.32/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.58  thf('4', plain,
% 4.32/4.58      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 4.32/4.58      inference('split', [status(esa)], ['3'])).
% 4.32/4.58  thf('5', plain,
% 4.32/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.32/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.58  thf(t56_tops_1, axiom,
% 4.32/4.58    (![A:$i]:
% 4.32/4.58     ( ( l1_pre_topc @ A ) =>
% 4.32/4.58       ( ![B:$i]:
% 4.32/4.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.32/4.58           ( ![C:$i]:
% 4.32/4.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.32/4.58               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 4.32/4.58                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 4.32/4.58  thf('6', plain,
% 4.32/4.58      (![X43 : $i, X44 : $i, X45 : $i]:
% 4.32/4.58         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 4.32/4.58          | ~ (v3_pre_topc @ X43 @ X44)
% 4.32/4.58          | ~ (r1_tarski @ X43 @ X45)
% 4.32/4.58          | (r1_tarski @ X43 @ (k1_tops_1 @ X44 @ X45))
% 4.32/4.58          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 4.32/4.58          | ~ (l1_pre_topc @ X44))),
% 4.32/4.58      inference('cnf', [status(esa)], [t56_tops_1])).
% 4.32/4.58  thf('7', plain,
% 4.32/4.58      (![X0 : $i]:
% 4.32/4.58         (~ (l1_pre_topc @ sk_A)
% 4.32/4.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.32/4.58          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 4.32/4.58          | ~ (r1_tarski @ sk_B @ X0)
% 4.32/4.58          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 4.32/4.58      inference('sup-', [status(thm)], ['5', '6'])).
% 4.32/4.58  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 4.32/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.58  thf('9', plain,
% 4.32/4.58      (![X0 : $i]:
% 4.32/4.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.32/4.58          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 4.32/4.58          | ~ (r1_tarski @ sk_B @ X0)
% 4.32/4.58          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 4.32/4.58      inference('demod', [status(thm)], ['7', '8'])).
% 4.32/4.58  thf('10', plain,
% 4.32/4.58      ((![X0 : $i]:
% 4.32/4.58          (~ (r1_tarski @ sk_B @ X0)
% 4.32/4.58           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 4.32/4.58           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 4.32/4.58         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 4.32/4.58      inference('sup-', [status(thm)], ['4', '9'])).
% 4.32/4.58  thf('11', plain,
% 4.32/4.58      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 4.32/4.58         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 4.32/4.58      inference('sup-', [status(thm)], ['2', '10'])).
% 4.32/4.58  thf(d10_xboole_0, axiom,
% 4.32/4.58    (![A:$i,B:$i]:
% 4.32/4.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.32/4.58  thf('12', plain,
% 4.32/4.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 4.32/4.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.32/4.58  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.32/4.58      inference('simplify', [status(thm)], ['12'])).
% 4.32/4.58  thf('14', plain,
% 4.32/4.58      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 4.32/4.58         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 4.32/4.58      inference('demod', [status(thm)], ['11', '13'])).
% 4.32/4.58  thf('15', plain,
% 4.32/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.32/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.58  thf(t44_tops_1, axiom,
% 4.32/4.58    (![A:$i]:
% 4.32/4.58     ( ( l1_pre_topc @ A ) =>
% 4.32/4.58       ( ![B:$i]:
% 4.32/4.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.32/4.58           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 4.32/4.58  thf('16', plain,
% 4.32/4.58      (![X41 : $i, X42 : $i]:
% 4.32/4.58         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 4.32/4.58          | (r1_tarski @ (k1_tops_1 @ X42 @ X41) @ X41)
% 4.32/4.58          | ~ (l1_pre_topc @ X42))),
% 4.32/4.58      inference('cnf', [status(esa)], [t44_tops_1])).
% 4.32/4.58  thf('17', plain,
% 4.32/4.58      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 4.32/4.58      inference('sup-', [status(thm)], ['15', '16'])).
% 4.32/4.58  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 4.32/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.58  thf('19', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 4.32/4.58      inference('demod', [status(thm)], ['17', '18'])).
% 4.32/4.58  thf('20', plain,
% 4.32/4.58      (![X0 : $i, X2 : $i]:
% 4.32/4.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.32/4.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.32/4.58  thf('21', plain,
% 4.32/4.58      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 4.32/4.58        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 4.32/4.58      inference('sup-', [status(thm)], ['19', '20'])).
% 4.32/4.58  thf('22', plain,
% 4.32/4.58      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 4.32/4.58         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 4.32/4.58      inference('sup-', [status(thm)], ['14', '21'])).
% 4.32/4.58  thf('23', plain,
% 4.32/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.32/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.58  thf(l78_tops_1, axiom,
% 4.32/4.58    (![A:$i]:
% 4.32/4.58     ( ( l1_pre_topc @ A ) =>
% 4.32/4.58       ( ![B:$i]:
% 4.32/4.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.32/4.58           ( ( k2_tops_1 @ A @ B ) =
% 4.32/4.58             ( k7_subset_1 @
% 4.32/4.58               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 4.32/4.58               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 4.32/4.58  thf('24', plain,
% 4.32/4.58      (![X39 : $i, X40 : $i]:
% 4.32/4.58         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 4.32/4.58          | ((k2_tops_1 @ X40 @ X39)
% 4.32/4.58              = (k7_subset_1 @ (u1_struct_0 @ X40) @ 
% 4.32/4.58                 (k2_pre_topc @ X40 @ X39) @ (k1_tops_1 @ X40 @ X39)))
% 4.32/4.58          | ~ (l1_pre_topc @ X40))),
% 4.32/4.58      inference('cnf', [status(esa)], [l78_tops_1])).
% 4.32/4.58  thf('25', plain,
% 4.32/4.58      ((~ (l1_pre_topc @ sk_A)
% 4.32/4.58        | ((k2_tops_1 @ sk_A @ sk_B)
% 4.32/4.58            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.32/4.58               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.32/4.58      inference('sup-', [status(thm)], ['23', '24'])).
% 4.32/4.58  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 4.32/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.58  thf('27', plain,
% 4.32/4.58      (((k2_tops_1 @ sk_A @ sk_B)
% 4.32/4.58         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.32/4.58            (k1_tops_1 @ sk_A @ sk_B)))),
% 4.32/4.58      inference('demod', [status(thm)], ['25', '26'])).
% 4.32/4.58  thf('28', plain,
% 4.32/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.32/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.58  thf(dt_k2_pre_topc, axiom,
% 4.32/4.58    (![A:$i,B:$i]:
% 4.32/4.58     ( ( ( l1_pre_topc @ A ) & 
% 4.32/4.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.32/4.58       ( m1_subset_1 @
% 4.32/4.58         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.32/4.58  thf('29', plain,
% 4.32/4.58      (![X33 : $i, X34 : $i]:
% 4.32/4.58         (~ (l1_pre_topc @ X33)
% 4.32/4.58          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 4.32/4.58          | (m1_subset_1 @ (k2_pre_topc @ X33 @ X34) @ 
% 4.32/4.58             (k1_zfmisc_1 @ (u1_struct_0 @ X33))))),
% 4.32/4.58      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 4.32/4.58  thf('30', plain,
% 4.32/4.58      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.32/4.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.32/4.58        | ~ (l1_pre_topc @ sk_A))),
% 4.32/4.58      inference('sup-', [status(thm)], ['28', '29'])).
% 4.32/4.58  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 4.32/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.58  thf('32', plain,
% 4.32/4.58      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.32/4.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.32/4.58      inference('demod', [status(thm)], ['30', '31'])).
% 4.32/4.58  thf(redefinition_k7_subset_1, axiom,
% 4.32/4.58    (![A:$i,B:$i,C:$i]:
% 4.32/4.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.32/4.58       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 4.32/4.58  thf('33', plain,
% 4.32/4.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.32/4.58         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 4.32/4.58          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 4.32/4.58      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 4.32/4.58  thf('34', plain,
% 4.32/4.58      (![X0 : $i]:
% 4.32/4.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.32/4.58           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 4.32/4.58      inference('sup-', [status(thm)], ['32', '33'])).
% 4.32/4.58  thf('35', plain,
% 4.32/4.58      (((k2_tops_1 @ sk_A @ sk_B)
% 4.32/4.58         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.32/4.58            (k1_tops_1 @ sk_A @ sk_B)))),
% 4.32/4.58      inference('demod', [status(thm)], ['27', '34'])).
% 4.32/4.58  thf('36', plain,
% 4.32/4.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 4.32/4.58          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 4.32/4.58         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 4.32/4.58      inference('sup+', [status(thm)], ['22', '35'])).
% 4.32/4.58  thf('37', plain,
% 4.32/4.58      (![X0 : $i]:
% 4.32/4.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.32/4.58           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 4.32/4.58      inference('sup-', [status(thm)], ['32', '33'])).
% 4.32/4.58  thf('38', plain,
% 4.32/4.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 4.32/4.58          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.32/4.58              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 4.32/4.58         <= (~
% 4.32/4.58             (((k2_tops_1 @ sk_A @ sk_B)
% 4.32/4.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.32/4.58                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.32/4.58      inference('split', [status(esa)], ['0'])).
% 4.32/4.58  thf('39', plain,
% 4.32/4.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 4.32/4.58          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 4.32/4.58         <= (~
% 4.32/4.58             (((k2_tops_1 @ sk_A @ sk_B)
% 4.32/4.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.32/4.58                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.32/4.58      inference('sup-', [status(thm)], ['37', '38'])).
% 4.32/4.58  thf('40', plain,
% 4.32/4.58      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 4.32/4.58         <= (~
% 4.32/4.58             (((k2_tops_1 @ sk_A @ sk_B)
% 4.32/4.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.32/4.58                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 4.32/4.58             ((v3_pre_topc @ sk_B @ sk_A)))),
% 4.32/4.58      inference('sup-', [status(thm)], ['36', '39'])).
% 4.32/4.58  thf('41', plain,
% 4.32/4.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 4.32/4.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.32/4.58             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 4.32/4.58       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 4.32/4.58      inference('simplify', [status(thm)], ['40'])).
% 4.32/4.58  thf('42', plain,
% 4.32/4.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 4.32/4.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.32/4.58             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 4.32/4.58       ((v3_pre_topc @ sk_B @ sk_A))),
% 4.32/4.58      inference('split', [status(esa)], ['3'])).
% 4.32/4.58  thf('43', plain,
% 4.32/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.32/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.58  thf(t74_tops_1, axiom,
% 4.32/4.58    (![A:$i]:
% 4.32/4.58     ( ( l1_pre_topc @ A ) =>
% 4.32/4.58       ( ![B:$i]:
% 4.32/4.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.32/4.58           ( ( k1_tops_1 @ A @ B ) =
% 4.32/4.58             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 4.32/4.58  thf('44', plain,
% 4.32/4.58      (![X46 : $i, X47 : $i]:
% 4.32/4.58         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 4.32/4.58          | ((k1_tops_1 @ X47 @ X46)
% 4.32/4.58              = (k7_subset_1 @ (u1_struct_0 @ X47) @ X46 @ 
% 4.32/4.58                 (k2_tops_1 @ X47 @ X46)))
% 4.32/4.58          | ~ (l1_pre_topc @ X47))),
% 4.32/4.58      inference('cnf', [status(esa)], [t74_tops_1])).
% 4.32/4.58  thf('45', plain,
% 4.32/4.58      ((~ (l1_pre_topc @ sk_A)
% 4.32/4.58        | ((k1_tops_1 @ sk_A @ sk_B)
% 4.32/4.58            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 4.32/4.58               (k2_tops_1 @ sk_A @ sk_B))))),
% 4.32/4.58      inference('sup-', [status(thm)], ['43', '44'])).
% 4.32/4.58  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 4.32/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.58  thf('47', plain,
% 4.32/4.58      (((k1_tops_1 @ sk_A @ sk_B)
% 4.32/4.58         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 4.32/4.58            (k2_tops_1 @ sk_A @ sk_B)))),
% 4.32/4.58      inference('demod', [status(thm)], ['45', '46'])).
% 4.32/4.58  thf('48', plain,
% 4.32/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.32/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.58  thf('49', plain,
% 4.32/4.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.32/4.58         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 4.32/4.58          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 4.32/4.58      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 4.32/4.58  thf('50', plain,
% 4.32/4.58      (![X0 : $i]:
% 4.32/4.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 4.32/4.58           = (k4_xboole_0 @ sk_B @ X0))),
% 4.32/4.58      inference('sup-', [status(thm)], ['48', '49'])).
% 4.32/4.58  thf('51', plain,
% 4.32/4.58      (((k1_tops_1 @ sk_A @ sk_B)
% 4.32/4.59         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 4.32/4.59      inference('demod', [status(thm)], ['47', '50'])).
% 4.32/4.59  thf(t48_xboole_1, axiom,
% 4.32/4.59    (![A:$i,B:$i]:
% 4.32/4.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.32/4.59  thf('52', plain,
% 4.32/4.59      (![X6 : $i, X7 : $i]:
% 4.32/4.59         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 4.32/4.59           = (k3_xboole_0 @ X6 @ X7))),
% 4.32/4.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.32/4.59  thf('53', plain,
% 4.32/4.59      (![X6 : $i, X7 : $i]:
% 4.32/4.59         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 4.32/4.59           = (k3_xboole_0 @ X6 @ X7))),
% 4.32/4.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.32/4.59  thf('54', plain,
% 4.32/4.59      (![X0 : $i, X1 : $i]:
% 4.32/4.59         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 4.32/4.59           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.32/4.59      inference('sup+', [status(thm)], ['52', '53'])).
% 4.32/4.59  thf('55', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.32/4.59      inference('simplify', [status(thm)], ['12'])).
% 4.32/4.59  thf(t3_subset, axiom,
% 4.32/4.59    (![A:$i,B:$i]:
% 4.32/4.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.32/4.59  thf('56', plain,
% 4.32/4.59      (![X27 : $i, X29 : $i]:
% 4.32/4.59         ((m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X27 @ X29))),
% 4.32/4.59      inference('cnf', [status(esa)], [t3_subset])).
% 4.32/4.59  thf('57', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.32/4.59      inference('sup-', [status(thm)], ['55', '56'])).
% 4.32/4.59  thf(dt_k7_subset_1, axiom,
% 4.32/4.59    (![A:$i,B:$i,C:$i]:
% 4.32/4.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.32/4.59       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.32/4.59  thf('58', plain,
% 4.32/4.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.32/4.59         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 4.32/4.59          | (m1_subset_1 @ (k7_subset_1 @ X13 @ X12 @ X14) @ 
% 4.32/4.59             (k1_zfmisc_1 @ X13)))),
% 4.32/4.59      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 4.32/4.59  thf('59', plain,
% 4.32/4.59      (![X0 : $i, X1 : $i]:
% 4.32/4.59         (m1_subset_1 @ (k7_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 4.32/4.59      inference('sup-', [status(thm)], ['57', '58'])).
% 4.32/4.59  thf('60', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.32/4.59      inference('sup-', [status(thm)], ['55', '56'])).
% 4.32/4.59  thf('61', plain,
% 4.32/4.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.32/4.59         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 4.32/4.59          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 4.32/4.59      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 4.32/4.59  thf('62', plain,
% 4.32/4.59      (![X0 : $i, X1 : $i]:
% 4.32/4.59         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 4.32/4.59      inference('sup-', [status(thm)], ['60', '61'])).
% 4.32/4.59  thf('63', plain,
% 4.32/4.59      (![X0 : $i, X1 : $i]:
% 4.32/4.59         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 4.32/4.59      inference('demod', [status(thm)], ['59', '62'])).
% 4.32/4.59  thf(involutiveness_k3_subset_1, axiom,
% 4.32/4.59    (![A:$i,B:$i]:
% 4.32/4.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.32/4.59       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 4.32/4.59  thf('64', plain,
% 4.32/4.59      (![X18 : $i, X19 : $i]:
% 4.32/4.59         (((k3_subset_1 @ X19 @ (k3_subset_1 @ X19 @ X18)) = (X18))
% 4.32/4.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 4.32/4.59      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 4.32/4.59  thf('65', plain,
% 4.32/4.59      (![X0 : $i, X1 : $i]:
% 4.32/4.59         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 4.32/4.59           = (k4_xboole_0 @ X0 @ X1))),
% 4.32/4.59      inference('sup-', [status(thm)], ['63', '64'])).
% 4.32/4.59  thf('66', plain,
% 4.32/4.59      (![X0 : $i, X1 : $i]:
% 4.32/4.59         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 4.32/4.59      inference('demod', [status(thm)], ['59', '62'])).
% 4.32/4.59  thf(d5_subset_1, axiom,
% 4.32/4.59    (![A:$i,B:$i]:
% 4.32/4.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.32/4.59       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 4.32/4.59  thf('67', plain,
% 4.32/4.59      (![X8 : $i, X9 : $i]:
% 4.32/4.59         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 4.32/4.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 4.32/4.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.32/4.59  thf('68', plain,
% 4.32/4.59      (![X0 : $i, X1 : $i]:
% 4.32/4.59         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.32/4.59           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 4.32/4.59      inference('sup-', [status(thm)], ['66', '67'])).
% 4.32/4.59  thf('69', plain,
% 4.32/4.59      (![X6 : $i, X7 : $i]:
% 4.32/4.59         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 4.32/4.59           = (k3_xboole_0 @ X6 @ X7))),
% 4.32/4.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.32/4.59  thf('70', plain,
% 4.32/4.59      (![X0 : $i, X1 : $i]:
% 4.32/4.59         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.32/4.59           = (k3_xboole_0 @ X0 @ X1))),
% 4.32/4.59      inference('demod', [status(thm)], ['68', '69'])).
% 4.32/4.59  thf('71', plain,
% 4.32/4.59      (![X0 : $i, X1 : $i]:
% 4.32/4.59         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 4.32/4.59           = (k4_xboole_0 @ X0 @ X1))),
% 4.32/4.59      inference('demod', [status(thm)], ['65', '70'])).
% 4.32/4.59  thf('72', plain,
% 4.32/4.59      (![X6 : $i, X7 : $i]:
% 4.32/4.59         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 4.32/4.59           = (k3_xboole_0 @ X6 @ X7))),
% 4.32/4.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.32/4.59  thf('73', plain,
% 4.32/4.59      (![X0 : $i, X1 : $i]:
% 4.32/4.59         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 4.32/4.59      inference('demod', [status(thm)], ['59', '62'])).
% 4.32/4.59  thf('74', plain,
% 4.32/4.59      (![X0 : $i, X1 : $i]:
% 4.32/4.59         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 4.32/4.59      inference('sup+', [status(thm)], ['72', '73'])).
% 4.32/4.59  thf('75', plain,
% 4.32/4.59      (![X8 : $i, X9 : $i]:
% 4.32/4.59         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 4.32/4.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 4.32/4.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.32/4.59  thf('76', plain,
% 4.32/4.59      (![X0 : $i, X1 : $i]:
% 4.32/4.59         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 4.32/4.59           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 4.32/4.59      inference('sup-', [status(thm)], ['74', '75'])).
% 4.32/4.59  thf('77', plain,
% 4.32/4.59      (![X0 : $i, X1 : $i]:
% 4.32/4.59         ((k4_xboole_0 @ X1 @ X0)
% 4.32/4.59           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 4.32/4.59      inference('sup+', [status(thm)], ['71', '76'])).
% 4.32/4.59  thf('78', plain,
% 4.32/4.59      (![X0 : $i, X1 : $i]:
% 4.32/4.59         ((k4_xboole_0 @ X1 @ X0)
% 4.32/4.59           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.32/4.59      inference('demod', [status(thm)], ['54', '77'])).
% 4.32/4.59  thf(t100_xboole_1, axiom,
% 4.32/4.59    (![A:$i,B:$i]:
% 4.32/4.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.32/4.59  thf('79', plain,
% 4.32/4.59      (![X3 : $i, X4 : $i]:
% 4.32/4.59         ((k4_xboole_0 @ X3 @ X4)
% 4.32/4.59           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 4.32/4.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.32/4.59  thf('80', plain,
% 4.32/4.59      (![X0 : $i, X1 : $i]:
% 4.32/4.59         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 4.32/4.59           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.32/4.59      inference('sup+', [status(thm)], ['78', '79'])).
% 4.32/4.59  thf('81', plain,
% 4.32/4.59      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 4.32/4.59         = (k5_xboole_0 @ sk_B @ 
% 4.32/4.59            (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 4.32/4.59      inference('sup+', [status(thm)], ['51', '80'])).
% 4.32/4.59  thf('82', plain,
% 4.32/4.59      (((k1_tops_1 @ sk_A @ sk_B)
% 4.32/4.59         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 4.32/4.59      inference('demod', [status(thm)], ['47', '50'])).
% 4.32/4.59  thf('83', plain,
% 4.32/4.59      (![X6 : $i, X7 : $i]:
% 4.32/4.59         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 4.32/4.59           = (k3_xboole_0 @ X6 @ X7))),
% 4.32/4.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.32/4.59  thf('84', plain,
% 4.32/4.59      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 4.32/4.59         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 4.32/4.59      inference('sup+', [status(thm)], ['82', '83'])).
% 4.41/4.59  thf('85', plain,
% 4.41/4.59      (((k1_tops_1 @ sk_A @ sk_B)
% 4.41/4.59         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 4.41/4.59      inference('demod', [status(thm)], ['47', '50'])).
% 4.41/4.59  thf('86', plain,
% 4.41/4.59      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 4.41/4.59         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 4.41/4.59      inference('demod', [status(thm)], ['81', '84', '85'])).
% 4.41/4.59  thf('87', plain,
% 4.41/4.59      (![X0 : $i, X1 : $i]:
% 4.41/4.59         ((k4_xboole_0 @ X1 @ X0)
% 4.41/4.59           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 4.41/4.59      inference('sup+', [status(thm)], ['71', '76'])).
% 4.41/4.59  thf('88', plain,
% 4.41/4.59      (((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 4.41/4.59         = (k4_xboole_0 @ sk_B @ 
% 4.41/4.59            (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.41/4.59      inference('sup+', [status(thm)], ['86', '87'])).
% 4.41/4.59  thf('89', plain,
% 4.41/4.59      (((k1_tops_1 @ sk_A @ sk_B)
% 4.41/4.59         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 4.41/4.59      inference('demod', [status(thm)], ['47', '50'])).
% 4.41/4.59  thf('90', plain,
% 4.41/4.59      (((k1_tops_1 @ sk_A @ sk_B)
% 4.41/4.59         = (k4_xboole_0 @ sk_B @ 
% 4.41/4.59            (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.41/4.59      inference('demod', [status(thm)], ['88', '89'])).
% 4.41/4.59  thf('91', plain,
% 4.41/4.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.41/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.41/4.59  thf(t48_pre_topc, axiom,
% 4.41/4.59    (![A:$i]:
% 4.41/4.59     ( ( l1_pre_topc @ A ) =>
% 4.41/4.59       ( ![B:$i]:
% 4.41/4.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.41/4.59           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 4.41/4.59  thf('92', plain,
% 4.41/4.59      (![X35 : $i, X36 : $i]:
% 4.41/4.59         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 4.41/4.59          | (r1_tarski @ X35 @ (k2_pre_topc @ X36 @ X35))
% 4.41/4.59          | ~ (l1_pre_topc @ X36))),
% 4.41/4.59      inference('cnf', [status(esa)], [t48_pre_topc])).
% 4.41/4.59  thf('93', plain,
% 4.41/4.59      ((~ (l1_pre_topc @ sk_A)
% 4.41/4.59        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.41/4.59      inference('sup-', [status(thm)], ['91', '92'])).
% 4.41/4.59  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 4.41/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.41/4.59  thf('95', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 4.41/4.59      inference('demod', [status(thm)], ['93', '94'])).
% 4.41/4.59  thf('96', plain,
% 4.41/4.59      (![X27 : $i, X29 : $i]:
% 4.41/4.59         ((m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X27 @ X29))),
% 4.41/4.59      inference('cnf', [status(esa)], [t3_subset])).
% 4.41/4.59  thf('97', plain,
% 4.41/4.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.41/4.59      inference('sup-', [status(thm)], ['95', '96'])).
% 4.41/4.59  thf('98', plain,
% 4.41/4.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.41/4.59         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 4.41/4.59          | (m1_subset_1 @ (k7_subset_1 @ X13 @ X12 @ X14) @ 
% 4.41/4.59             (k1_zfmisc_1 @ X13)))),
% 4.41/4.59      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 4.41/4.59  thf('99', plain,
% 4.41/4.59      (![X0 : $i]:
% 4.41/4.59         (m1_subset_1 @ 
% 4.41/4.59          (k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ X0) @ 
% 4.41/4.59          (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.41/4.59      inference('sup-', [status(thm)], ['97', '98'])).
% 4.41/4.59  thf('100', plain,
% 4.41/4.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.41/4.59      inference('sup-', [status(thm)], ['95', '96'])).
% 4.41/4.59  thf('101', plain,
% 4.41/4.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.41/4.59         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 4.41/4.59          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 4.41/4.59      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 4.41/4.59  thf('102', plain,
% 4.41/4.59      (![X0 : $i]:
% 4.41/4.59         ((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ X0)
% 4.41/4.59           = (k4_xboole_0 @ sk_B @ X0))),
% 4.41/4.59      inference('sup-', [status(thm)], ['100', '101'])).
% 4.41/4.59  thf('103', plain,
% 4.41/4.59      (![X0 : $i]:
% 4.41/4.59         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 4.41/4.59          (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.41/4.59      inference('demod', [status(thm)], ['99', '102'])).
% 4.41/4.59  thf('104', plain,
% 4.41/4.59      (![X18 : $i, X19 : $i]:
% 4.41/4.59         (((k3_subset_1 @ X19 @ (k3_subset_1 @ X19 @ X18)) = (X18))
% 4.41/4.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 4.41/4.59      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 4.41/4.59  thf('105', plain,
% 4.41/4.59      (![X0 : $i]:
% 4.41/4.59         ((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.41/4.59           (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.41/4.59            (k4_xboole_0 @ sk_B @ X0)))
% 4.41/4.59           = (k4_xboole_0 @ sk_B @ X0))),
% 4.41/4.59      inference('sup-', [status(thm)], ['103', '104'])).
% 4.41/4.59  thf('106', plain,
% 4.41/4.59      (![X0 : $i]:
% 4.41/4.59         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 4.41/4.59          (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.41/4.59      inference('demod', [status(thm)], ['99', '102'])).
% 4.41/4.59  thf('107', plain,
% 4.41/4.59      (![X8 : $i, X9 : $i]:
% 4.41/4.59         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 4.41/4.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 4.41/4.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.41/4.59  thf('108', plain,
% 4.41/4.59      (![X0 : $i]:
% 4.41/4.59         ((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.41/4.59           (k4_xboole_0 @ sk_B @ X0))
% 4.41/4.59           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.41/4.59              (k4_xboole_0 @ sk_B @ X0)))),
% 4.41/4.59      inference('sup-', [status(thm)], ['106', '107'])).
% 4.41/4.59  thf('109', plain,
% 4.41/4.59      (![X0 : $i, X1 : $i]:
% 4.41/4.59         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.41/4.59           = (k3_xboole_0 @ X0 @ X1))),
% 4.41/4.59      inference('demod', [status(thm)], ['68', '69'])).
% 4.41/4.59  thf('110', plain,
% 4.41/4.59      (![X0 : $i]:
% 4.41/4.59         ((k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.41/4.59           (k4_xboole_0 @ sk_B @ X0)) = (k4_xboole_0 @ sk_B @ X0))),
% 4.41/4.59      inference('demod', [status(thm)], ['105', '108', '109'])).
% 4.41/4.59  thf('111', plain,
% 4.41/4.59      (((k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 4.41/4.59         = (k4_xboole_0 @ sk_B @ 
% 4.41/4.59            (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.41/4.59      inference('sup+', [status(thm)], ['90', '110'])).
% 4.41/4.59  thf('112', plain,
% 4.41/4.59      (((k1_tops_1 @ sk_A @ sk_B)
% 4.41/4.59         = (k4_xboole_0 @ sk_B @ 
% 4.41/4.59            (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.41/4.59      inference('demod', [status(thm)], ['88', '89'])).
% 4.41/4.59  thf('113', plain,
% 4.41/4.59      (((k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 4.41/4.59         = (k1_tops_1 @ sk_A @ sk_B))),
% 4.41/4.59      inference('demod', [status(thm)], ['111', '112'])).
% 4.41/4.59  thf('114', plain,
% 4.41/4.59      (((k2_tops_1 @ sk_A @ sk_B)
% 4.41/4.59         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.41/4.59            (k1_tops_1 @ sk_A @ sk_B)))),
% 4.41/4.59      inference('demod', [status(thm)], ['27', '34'])).
% 4.41/4.59  thf('115', plain,
% 4.41/4.59      (![X6 : $i, X7 : $i]:
% 4.41/4.59         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 4.41/4.59           = (k3_xboole_0 @ X6 @ X7))),
% 4.41/4.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.41/4.59  thf('116', plain,
% 4.41/4.59      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 4.41/4.59         = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.41/4.59            (k1_tops_1 @ sk_A @ sk_B)))),
% 4.41/4.59      inference('sup+', [status(thm)], ['114', '115'])).
% 4.41/4.59  thf('117', plain,
% 4.41/4.59      (![X0 : $i]:
% 4.41/4.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.41/4.59           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 4.41/4.59      inference('sup-', [status(thm)], ['32', '33'])).
% 4.41/4.59  thf('118', plain,
% 4.41/4.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 4.41/4.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.41/4.59             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 4.41/4.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 4.41/4.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.41/4.59                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.41/4.59      inference('split', [status(esa)], ['3'])).
% 4.41/4.59  thf('119', plain,
% 4.41/4.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 4.41/4.59          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 4.41/4.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 4.41/4.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.41/4.59                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.41/4.59      inference('sup+', [status(thm)], ['117', '118'])).
% 4.41/4.59  thf('120', plain,
% 4.41/4.59      (![X6 : $i, X7 : $i]:
% 4.41/4.59         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 4.41/4.59           = (k3_xboole_0 @ X6 @ X7))),
% 4.41/4.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.41/4.59  thf('121', plain,
% 4.41/4.59      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 4.41/4.59          = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 4.41/4.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 4.41/4.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.41/4.59                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.41/4.59      inference('sup+', [status(thm)], ['119', '120'])).
% 4.41/4.59  thf('122', plain,
% 4.41/4.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.41/4.59      inference('sup-', [status(thm)], ['95', '96'])).
% 4.41/4.59  thf('123', plain,
% 4.41/4.59      (![X18 : $i, X19 : $i]:
% 4.41/4.59         (((k3_subset_1 @ X19 @ (k3_subset_1 @ X19 @ X18)) = (X18))
% 4.41/4.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 4.41/4.59      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 4.41/4.59  thf('124', plain,
% 4.41/4.59      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.41/4.59         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 4.41/4.59      inference('sup-', [status(thm)], ['122', '123'])).
% 4.41/4.59  thf('125', plain,
% 4.41/4.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.41/4.59      inference('sup-', [status(thm)], ['95', '96'])).
% 4.41/4.59  thf('126', plain,
% 4.41/4.59      (![X8 : $i, X9 : $i]:
% 4.41/4.59         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 4.41/4.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 4.41/4.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.41/4.59  thf('127', plain,
% 4.41/4.59      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 4.41/4.59         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 4.41/4.59      inference('sup-', [status(thm)], ['125', '126'])).
% 4.41/4.59  thf('128', plain,
% 4.41/4.59      (![X0 : $i, X1 : $i]:
% 4.41/4.59         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.41/4.59           = (k3_xboole_0 @ X0 @ X1))),
% 4.41/4.59      inference('demod', [status(thm)], ['68', '69'])).
% 4.41/4.59  thf('129', plain,
% 4.41/4.59      (((k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B) = (sk_B))),
% 4.41/4.59      inference('demod', [status(thm)], ['124', '127', '128'])).
% 4.41/4.59  thf('130', plain,
% 4.41/4.59      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 4.41/4.59          = (sk_B)))
% 4.41/4.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 4.41/4.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.41/4.59                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.41/4.59      inference('demod', [status(thm)], ['121', '129'])).
% 4.41/4.59  thf('131', plain,
% 4.41/4.59      ((((k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 4.41/4.59          = (sk_B)))
% 4.41/4.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 4.41/4.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.41/4.59                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.41/4.59      inference('sup+', [status(thm)], ['116', '130'])).
% 4.41/4.59  thf('132', plain,
% 4.41/4.59      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 4.41/4.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 4.41/4.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.41/4.59                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.41/4.59      inference('sup+', [status(thm)], ['113', '131'])).
% 4.41/4.59  thf('133', plain,
% 4.41/4.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.41/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.41/4.59  thf(fc9_tops_1, axiom,
% 4.41/4.59    (![A:$i,B:$i]:
% 4.41/4.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 4.41/4.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.41/4.59       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 4.41/4.59  thf('134', plain,
% 4.41/4.59      (![X37 : $i, X38 : $i]:
% 4.41/4.59         (~ (l1_pre_topc @ X37)
% 4.41/4.59          | ~ (v2_pre_topc @ X37)
% 4.41/4.59          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 4.41/4.59          | (v3_pre_topc @ (k1_tops_1 @ X37 @ X38) @ X37))),
% 4.41/4.59      inference('cnf', [status(esa)], [fc9_tops_1])).
% 4.41/4.59  thf('135', plain,
% 4.41/4.59      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 4.41/4.59        | ~ (v2_pre_topc @ sk_A)
% 4.41/4.59        | ~ (l1_pre_topc @ sk_A))),
% 4.41/4.59      inference('sup-', [status(thm)], ['133', '134'])).
% 4.41/4.59  thf('136', plain, ((v2_pre_topc @ sk_A)),
% 4.41/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.41/4.59  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 4.41/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.41/4.59  thf('138', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 4.41/4.59      inference('demod', [status(thm)], ['135', '136', '137'])).
% 4.41/4.59  thf('139', plain,
% 4.41/4.59      (((v3_pre_topc @ sk_B @ sk_A))
% 4.41/4.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 4.41/4.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.41/4.59                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.41/4.59      inference('sup+', [status(thm)], ['132', '138'])).
% 4.41/4.59  thf('140', plain,
% 4.41/4.59      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 4.41/4.59      inference('split', [status(esa)], ['0'])).
% 4.41/4.59  thf('141', plain,
% 4.41/4.59      (~
% 4.41/4.59       (((k2_tops_1 @ sk_A @ sk_B)
% 4.41/4.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.41/4.59             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 4.41/4.59       ((v3_pre_topc @ sk_B @ sk_A))),
% 4.41/4.59      inference('sup-', [status(thm)], ['139', '140'])).
% 4.41/4.59  thf('142', plain, ($false),
% 4.41/4.59      inference('sat_resolution*', [status(thm)], ['1', '41', '42', '141'])).
% 4.41/4.59  
% 4.41/4.59  % SZS output end Refutation
% 4.41/4.59  
% 4.41/4.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
