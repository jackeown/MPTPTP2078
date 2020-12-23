%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D9F9RMxQo6

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:25 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 179 expanded)
%              Number of leaves         :   28 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :  556 (1716 expanded)
%              Number of equality atoms :   40 (  69 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t88_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_tops_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( ( k1_tops_1 @ X43 @ X42 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X43 ) @ X42 @ ( k2_tops_1 @ X43 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('20',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( ( k1_tops_1 @ X45 @ X44 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X44 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','27'])).

thf('29',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf('30',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('31',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v2_tops_1 @ X44 @ X45 )
      | ( ( k1_tops_1 @ X45 @ X44 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('39',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','27','38'])).

thf('40',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','39'])).

thf('41',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','40'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('46',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('51',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['45','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['29','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D9F9RMxQo6
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:11:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.76/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.96  % Solved by: fo/fo7.sh
% 0.76/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.96  % done 2034 iterations in 0.521s
% 0.76/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.96  % SZS output start Refutation
% 0.76/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.96  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.76/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.96  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.96  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.76/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.96  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.76/0.96  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.76/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.76/0.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.96  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.76/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.96  thf(t88_tops_1, conjecture,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( l1_pre_topc @ A ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96           ( ( v2_tops_1 @ B @ A ) <=>
% 0.76/0.96             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.96    (~( ![A:$i]:
% 0.76/0.96        ( ( l1_pre_topc @ A ) =>
% 0.76/0.96          ( ![B:$i]:
% 0.76/0.96            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96              ( ( v2_tops_1 @ B @ A ) <=>
% 0.76/0.96                ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.76/0.96    inference('cnf.neg', [status(esa)], [t88_tops_1])).
% 0.76/0.96  thf('0', plain,
% 0.76/0.96      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.76/0.96        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('1', plain,
% 0.76/0.96      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.76/0.96         <= (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.76/0.96      inference('split', [status(esa)], ['0'])).
% 0.76/0.96  thf('2', plain,
% 0.76/0.96      (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.76/0.96       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.76/0.96      inference('split', [status(esa)], ['0'])).
% 0.76/0.96  thf('3', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(t74_tops_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( l1_pre_topc @ A ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96           ( ( k1_tops_1 @ A @ B ) =
% 0.76/0.96             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.76/0.96  thf('4', plain,
% 0.76/0.96      (![X42 : $i, X43 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.76/0.96          | ((k1_tops_1 @ X43 @ X42)
% 0.76/0.96              = (k7_subset_1 @ (u1_struct_0 @ X43) @ X42 @ 
% 0.76/0.96                 (k2_tops_1 @ X43 @ X42)))
% 0.76/0.96          | ~ (l1_pre_topc @ X43))),
% 0.76/0.96      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.76/0.96  thf('5', plain,
% 0.76/0.96      ((~ (l1_pre_topc @ sk_A)
% 0.76/0.96        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.76/0.96            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.96               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.96  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('7', plain,
% 0.76/0.96      (((k1_tops_1 @ sk_A @ sk_B)
% 0.76/0.96         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.96            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('demod', [status(thm)], ['5', '6'])).
% 0.76/0.96  thf('8', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(redefinition_k7_subset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.96       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.76/0.96  thf('9', plain,
% 0.76/0.96      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.76/0.96          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.76/0.96  thf('10', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.76/0.96           = (k4_xboole_0 @ sk_B @ X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['8', '9'])).
% 0.76/0.96  thf('11', plain,
% 0.76/0.96      (((k1_tops_1 @ sk_A @ sk_B)
% 0.76/0.96         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('demod', [status(thm)], ['7', '10'])).
% 0.76/0.96  thf('12', plain,
% 0.76/0.96      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.76/0.96        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('13', plain,
% 0.76/0.96      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.76/0.96         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.76/0.96      inference('split', [status(esa)], ['12'])).
% 0.76/0.96  thf(t12_xboole_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.76/0.96  thf('14', plain,
% 0.76/0.96      (![X5 : $i, X6 : $i]:
% 0.76/0.96         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.76/0.96      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.96  thf('15', plain,
% 0.76/0.96      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.76/0.96          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.76/0.96         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['13', '14'])).
% 0.76/0.96  thf(t46_xboole_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.76/0.96  thf('16', plain,
% 0.76/0.96      (![X14 : $i, X15 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 0.76/0.96      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.76/0.96  thf('17', plain,
% 0.76/0.96      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0)))
% 0.76/0.96         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.76/0.96      inference('sup+', [status(thm)], ['15', '16'])).
% 0.76/0.96  thf('18', plain,
% 0.76/0.96      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.76/0.96         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.76/0.96      inference('sup+', [status(thm)], ['11', '17'])).
% 0.76/0.96  thf('19', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(t84_tops_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( l1_pre_topc @ A ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96           ( ( v2_tops_1 @ B @ A ) <=>
% 0.76/0.96             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.76/0.96  thf('20', plain,
% 0.76/0.96      (![X44 : $i, X45 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.76/0.96          | ((k1_tops_1 @ X45 @ X44) != (k1_xboole_0))
% 0.76/0.96          | (v2_tops_1 @ X44 @ X45)
% 0.76/0.96          | ~ (l1_pre_topc @ X45))),
% 0.76/0.96      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.76/0.96  thf('21', plain,
% 0.76/0.96      ((~ (l1_pre_topc @ sk_A)
% 0.76/0.96        | (v2_tops_1 @ sk_B @ sk_A)
% 0.76/0.96        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['19', '20'])).
% 0.76/0.96  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('23', plain,
% 0.76/0.96      (((v2_tops_1 @ sk_B @ sk_A)
% 0.76/0.96        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.76/0.96      inference('demod', [status(thm)], ['21', '22'])).
% 0.76/0.96  thf('24', plain,
% 0.76/0.96      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.76/0.96         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['18', '23'])).
% 0.76/0.96  thf('25', plain,
% 0.76/0.96      (((v2_tops_1 @ sk_B @ sk_A))
% 0.76/0.96         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.76/0.96      inference('simplify', [status(thm)], ['24'])).
% 0.76/0.96  thf('26', plain,
% 0.76/0.96      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.76/0.96      inference('split', [status(esa)], ['0'])).
% 0.76/0.96  thf('27', plain,
% 0.76/0.96      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.76/0.96       ~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.96  thf('28', plain, (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('sat_resolution*', [status(thm)], ['2', '27'])).
% 0.76/0.96  thf('29', plain, (~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.76/0.96      inference('simpl_trail', [status(thm)], ['1', '28'])).
% 0.76/0.96  thf('30', plain,
% 0.76/0.96      (((k1_tops_1 @ sk_A @ sk_B)
% 0.76/0.96         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('demod', [status(thm)], ['7', '10'])).
% 0.76/0.96  thf('31', plain,
% 0.76/0.96      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.76/0.96      inference('split', [status(esa)], ['12'])).
% 0.76/0.96  thf('32', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('33', plain,
% 0.76/0.96      (![X44 : $i, X45 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.76/0.96          | ~ (v2_tops_1 @ X44 @ X45)
% 0.76/0.96          | ((k1_tops_1 @ X45 @ X44) = (k1_xboole_0))
% 0.76/0.96          | ~ (l1_pre_topc @ X45))),
% 0.76/0.96      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.76/0.96  thf('34', plain,
% 0.76/0.96      ((~ (l1_pre_topc @ sk_A)
% 0.76/0.96        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.76/0.96        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['32', '33'])).
% 0.76/0.96  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('36', plain,
% 0.76/0.96      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.76/0.96        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['34', '35'])).
% 0.76/0.96  thf('37', plain,
% 0.76/0.96      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.76/0.96         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['31', '36'])).
% 0.76/0.96  thf('38', plain,
% 0.76/0.96      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.76/0.96       ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('split', [status(esa)], ['12'])).
% 0.76/0.96  thf('39', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.76/0.96      inference('sat_resolution*', [status(thm)], ['2', '27', '38'])).
% 0.76/0.96  thf('40', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.76/0.96      inference('simpl_trail', [status(thm)], ['37', '39'])).
% 0.76/0.96  thf('41', plain,
% 0.76/0.96      (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('demod', [status(thm)], ['30', '40'])).
% 0.76/0.96  thf(t48_xboole_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.76/0.96  thf('42', plain,
% 0.76/0.96      (![X16 : $i, X17 : $i]:
% 0.76/0.96         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.76/0.96           = (k3_xboole_0 @ X16 @ X17))),
% 0.76/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.96  thf('43', plain,
% 0.76/0.96      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 0.76/0.96         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('sup+', [status(thm)], ['41', '42'])).
% 0.76/0.96  thf(t3_boole, axiom,
% 0.76/0.96    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.76/0.96  thf('44', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.76/0.96      inference('cnf', [status(esa)], [t3_boole])).
% 0.76/0.96  thf('45', plain,
% 0.76/0.96      (((sk_B) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('demod', [status(thm)], ['43', '44'])).
% 0.76/0.96  thf(commutativity_k2_tarski, axiom,
% 0.76/0.96    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.76/0.96  thf('46', plain,
% 0.76/0.96      (![X20 : $i, X21 : $i]:
% 0.76/0.96         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 0.76/0.96      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.76/0.96  thf(t12_setfam_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.76/0.96  thf('47', plain,
% 0.76/0.96      (![X31 : $i, X32 : $i]:
% 0.76/0.96         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.76/0.96      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.76/0.96  thf('48', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.96      inference('sup+', [status(thm)], ['46', '47'])).
% 0.76/0.96  thf('49', plain,
% 0.76/0.96      (![X31 : $i, X32 : $i]:
% 0.76/0.96         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.76/0.96      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.76/0.96  thf('50', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.96      inference('sup+', [status(thm)], ['48', '49'])).
% 0.76/0.96  thf(t17_xboole_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.76/0.96  thf('51', plain,
% 0.76/0.96      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.76/0.96      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.76/0.96  thf('52', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.76/0.96      inference('sup+', [status(thm)], ['50', '51'])).
% 0.76/0.96  thf('53', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['45', '52'])).
% 0.76/0.96  thf('54', plain, ($false), inference('demod', [status(thm)], ['29', '53'])).
% 0.76/0.96  
% 0.76/0.96  % SZS output end Refutation
% 0.76/0.96  
% 0.76/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
