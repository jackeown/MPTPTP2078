%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BKIsrXDjRj

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:45 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 126 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  581 (1363 expanded)
%              Number of equality atoms :   31 (  40 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(t103_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v5_tops_1 @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t103_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
          <=> ( B
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v5_tops_1 @ X42 @ X43 )
      | ( X42
        = ( k2_pre_topc @ X43 @ ( k1_tops_1 @ X43 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X46 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k4_subset_1 @ X38 @ X37 @ X39 )
        = ( k2_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('16',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k4_subset_1 @ X38 @ X37 @ X39 )
        = ( k3_tarski @ ( k2_tarski @ X37 @ X39 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k2_pre_topc @ X49 @ X48 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 @ ( k2_tops_1 @ X49 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( l1_pre_topc @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X44 @ X45 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k2_pre_topc @ X40 @ ( k2_pre_topc @ X40 @ X41 ) )
        = ( k2_pre_topc @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('29',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('33',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('34',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','34'])).

thf('36',plain,
    ( sk_B
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['18','35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['37'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('41',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('44',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('45',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X5 @ X7 ) ) @ X6 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['36','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['7','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BKIsrXDjRj
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 209 iterations in 0.156s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.57  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.38/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.57  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.38/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.57  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.38/0.57  thf(t103_tops_1, conjecture,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_pre_topc @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( ( v5_tops_1 @ B @ A ) =>
% 0.38/0.57             ( r1_tarski @
% 0.38/0.57               ( k2_tops_1 @ A @ B ) @ 
% 0.38/0.57               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i]:
% 0.38/0.57        ( ( l1_pre_topc @ A ) =>
% 0.38/0.57          ( ![B:$i]:
% 0.38/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57              ( ( v5_tops_1 @ B @ A ) =>
% 0.38/0.57                ( r1_tarski @
% 0.38/0.57                  ( k2_tops_1 @ A @ B ) @ 
% 0.38/0.57                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.38/0.57          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d7_tops_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_pre_topc @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( ( v5_tops_1 @ B @ A ) <=>
% 0.38/0.57             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X42 : $i, X43 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.38/0.57          | ~ (v5_tops_1 @ X42 @ X43)
% 0.38/0.57          | ((X42) = (k2_pre_topc @ X43 @ (k1_tops_1 @ X43 @ X42)))
% 0.38/0.57          | ~ (l1_pre_topc @ X43))),
% 0.38/0.57      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.38/0.57        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.57  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.38/0.57  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.38/0.57      inference('demod', [status(thm)], ['0', '6'])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(dt_k2_tops_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( l1_pre_topc @ A ) & 
% 0.38/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.57       ( m1_subset_1 @
% 0.38/0.57         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (![X46 : $i, X47 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ X46)
% 0.38/0.57          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.38/0.57          | (m1_subset_1 @ (k2_tops_1 @ X46 @ X47) @ 
% 0.38/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X46))))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.38/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.57  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.38/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k4_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.38/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.57       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 0.38/0.57          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38))
% 0.38/0.57          | ((k4_subset_1 @ X38 @ X37 @ X39) = (k2_xboole_0 @ X37 @ X39)))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.38/0.57  thf(l51_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (![X35 : $i, X36 : $i]:
% 0.38/0.57         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.38/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 0.38/0.57          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38))
% 0.38/0.57          | ((k4_subset_1 @ X38 @ X37 @ X39)
% 0.38/0.57              = (k3_tarski @ (k2_tarski @ X37 @ X39))))),
% 0.38/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.57            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['13', '16'])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.38/0.57         = (k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['12', '17'])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t65_tops_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_pre_topc @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( ( k2_pre_topc @ A @ B ) =
% 0.38/0.57             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X48 : $i, X49 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.38/0.57          | ((k2_pre_topc @ X49 @ X48)
% 0.38/0.57              = (k4_subset_1 @ (u1_struct_0 @ X49) @ X48 @ 
% 0.38/0.57                 (k2_tops_1 @ X49 @ X48)))
% 0.38/0.57          | ~ (l1_pre_topc @ X49))),
% 0.38/0.57      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.38/0.57            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.57  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(dt_k1_tops_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( l1_pre_topc @ A ) & 
% 0.38/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.57       ( m1_subset_1 @
% 0.38/0.57         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      (![X44 : $i, X45 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ X44)
% 0.38/0.57          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.38/0.57          | (m1_subset_1 @ (k1_tops_1 @ X44 @ X45) @ 
% 0.38/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X44))))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.38/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.57  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.38/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.38/0.57  thf(projectivity_k2_pre_topc, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( l1_pre_topc @ A ) & 
% 0.38/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.57       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.38/0.57         ( k2_pre_topc @ A @ B ) ) ))).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X40 : $i, X41 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ X40)
% 0.38/0.57          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.38/0.57          | ((k2_pre_topc @ X40 @ (k2_pre_topc @ X40 @ X41))
% 0.38/0.57              = (k2_pre_topc @ X40 @ X41)))),
% 0.38/0.57      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.38/0.57          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.57  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.38/0.57         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.38/0.57  thf('34', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (((sk_B)
% 0.38/0.57         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['21', '22', '34'])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      (((sk_B) = (k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['18', '35'])).
% 0.38/0.57  thf(d10_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.57  thf('38', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.38/0.57      inference('simplify', [status(thm)], ['37'])).
% 0.38/0.57  thf(commutativity_k2_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (![X35 : $i, X36 : $i]:
% 0.38/0.57         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.38/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (![X35 : $i, X36 : $i]:
% 0.38/0.57         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.38/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 0.38/0.57           = (k3_tarski @ (k2_tarski @ X0 @ X1)))),
% 0.38/0.57      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.38/0.57  thf(t11_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.57         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (![X35 : $i, X36 : $i]:
% 0.38/0.57         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.38/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.57         ((r1_tarski @ X5 @ X6)
% 0.38/0.57          | ~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X5 @ X7)) @ X6))),
% 0.38/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X2)
% 0.38/0.57          | (r1_tarski @ X0 @ X2))),
% 0.38/0.57      inference('sup-', [status(thm)], ['42', '45'])).
% 0.38/0.57  thf('47', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['38', '46'])).
% 0.38/0.57  thf('48', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.38/0.57      inference('sup+', [status(thm)], ['36', '47'])).
% 0.38/0.57  thf('49', plain, ($false), inference('demod', [status(thm)], ['7', '48'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
