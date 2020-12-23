%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GE9EAqVffS

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:46 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 121 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  517 (1289 expanded)
%              Number of equality atoms :   28 (  36 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v5_tops_1 @ X44 @ X45 )
      | ( X44
        = ( k2_pre_topc @ X45 @ ( k1_tops_1 @ X45 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
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

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('9',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X51 @ X50 ) @ X50 )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('26',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k2_tops_1 @ X49 @ X48 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X49 ) @ ( k2_pre_topc @ X49 @ X48 ) @ ( k1_tops_1 @ X49 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('30',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X46 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( l1_pre_topc @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k2_pre_topc @ X42 @ ( k2_pre_topc @ X42 @ X43 ) )
        = ( k2_pre_topc @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('35',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('39',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('40',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('42',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k7_subset_1 @ X38 @ X37 @ X39 )
        = ( k4_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28','40','43'])).

thf('45',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['24','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['7','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GE9EAqVffS
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:47:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.40/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.57  % Solved by: fo/fo7.sh
% 0.40/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.57  % done 230 iterations in 0.105s
% 0.40/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.57  % SZS output start Refutation
% 0.40/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.57  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.40/0.57  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.40/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.57  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.40/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.40/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.57  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.40/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.57  thf(t103_tops_1, conjecture,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( l1_pre_topc @ A ) =>
% 0.40/0.57       ( ![B:$i]:
% 0.40/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.57           ( ( v5_tops_1 @ B @ A ) =>
% 0.40/0.57             ( r1_tarski @
% 0.40/0.57               ( k2_tops_1 @ A @ B ) @ 
% 0.40/0.57               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.57    (~( ![A:$i]:
% 0.40/0.57        ( ( l1_pre_topc @ A ) =>
% 0.40/0.57          ( ![B:$i]:
% 0.40/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.57              ( ( v5_tops_1 @ B @ A ) =>
% 0.40/0.57                ( r1_tarski @
% 0.40/0.57                  ( k2_tops_1 @ A @ B ) @ 
% 0.40/0.57                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.40/0.57    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 0.40/0.57  thf('0', plain,
% 0.40/0.57      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.40/0.57          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('1', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(d7_tops_1, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( l1_pre_topc @ A ) =>
% 0.40/0.57       ( ![B:$i]:
% 0.40/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.57           ( ( v5_tops_1 @ B @ A ) <=>
% 0.40/0.57             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.57  thf('2', plain,
% 0.40/0.57      (![X44 : $i, X45 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.40/0.57          | ~ (v5_tops_1 @ X44 @ X45)
% 0.40/0.57          | ((X44) = (k2_pre_topc @ X45 @ (k1_tops_1 @ X45 @ X44)))
% 0.40/0.57          | ~ (l1_pre_topc @ X45))),
% 0.40/0.57      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.40/0.57  thf('3', plain,
% 0.40/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.57        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.40/0.57        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.57  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('6', plain,
% 0.40/0.57      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.57      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.40/0.57  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.40/0.57      inference('demod', [status(thm)], ['0', '6'])).
% 0.40/0.57  thf('8', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(t44_tops_1, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( l1_pre_topc @ A ) =>
% 0.40/0.57       ( ![B:$i]:
% 0.40/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.57           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.40/0.57  thf('9', plain,
% 0.40/0.57      (![X50 : $i, X51 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.40/0.57          | (r1_tarski @ (k1_tops_1 @ X51 @ X50) @ X50)
% 0.40/0.57          | ~ (l1_pre_topc @ X51))),
% 0.40/0.57      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.40/0.57  thf('10', plain,
% 0.40/0.57      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.40/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.57  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('12', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.40/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.40/0.57  thf(t12_xboole_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.40/0.57  thf('13', plain,
% 0.40/0.57      (![X4 : $i, X5 : $i]:
% 0.40/0.57         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.40/0.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.40/0.57  thf('14', plain,
% 0.40/0.57      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B))),
% 0.40/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.57  thf(commutativity_k2_xboole_0, axiom,
% 0.40/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.40/0.57  thf('15', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.40/0.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.40/0.57  thf('16', plain,
% 0.40/0.57      (((k2_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.40/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.40/0.57  thf('17', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.40/0.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.40/0.57  thf(t39_xboole_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.40/0.57  thf('18', plain,
% 0.40/0.57      (![X6 : $i, X7 : $i]:
% 0.40/0.57         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.40/0.57           = (k2_xboole_0 @ X6 @ X7))),
% 0.40/0.57      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.40/0.57  thf('19', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.40/0.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.40/0.57  thf(t7_xboole_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.40/0.57  thf('20', plain,
% 0.40/0.57      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.40/0.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.40/0.57  thf('21', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['19', '20'])).
% 0.40/0.57  thf('22', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['18', '21'])).
% 0.40/0.57  thf('23', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['17', '22'])).
% 0.40/0.57  thf('24', plain,
% 0.40/0.57      ((r1_tarski @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)),
% 0.40/0.57      inference('sup+', [status(thm)], ['16', '23'])).
% 0.40/0.57  thf('25', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(l78_tops_1, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( l1_pre_topc @ A ) =>
% 0.40/0.57       ( ![B:$i]:
% 0.40/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.57           ( ( k2_tops_1 @ A @ B ) =
% 0.40/0.57             ( k7_subset_1 @
% 0.40/0.57               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.40/0.57               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.40/0.57  thf('26', plain,
% 0.40/0.57      (![X48 : $i, X49 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.40/0.57          | ((k2_tops_1 @ X49 @ X48)
% 0.40/0.57              = (k7_subset_1 @ (u1_struct_0 @ X49) @ 
% 0.40/0.57                 (k2_pre_topc @ X49 @ X48) @ (k1_tops_1 @ X49 @ X48)))
% 0.40/0.57          | ~ (l1_pre_topc @ X49))),
% 0.40/0.57      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.40/0.57  thf('27', plain,
% 0.40/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.57        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.57            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.57  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('29', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(dt_k1_tops_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ( l1_pre_topc @ A ) & 
% 0.40/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.40/0.57       ( m1_subset_1 @
% 0.40/0.57         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.40/0.57  thf('30', plain,
% 0.40/0.57      (![X46 : $i, X47 : $i]:
% 0.40/0.57         (~ (l1_pre_topc @ X46)
% 0.40/0.57          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.40/0.57          | (m1_subset_1 @ (k1_tops_1 @ X46 @ X47) @ 
% 0.40/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X46))))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.40/0.57  thf('31', plain,
% 0.40/0.57      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.40/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.57  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('33', plain,
% 0.40/0.57      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.40/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.57  thf(projectivity_k2_pre_topc, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ( l1_pre_topc @ A ) & 
% 0.40/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.40/0.57       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.40/0.57         ( k2_pre_topc @ A @ B ) ) ))).
% 0.40/0.57  thf('34', plain,
% 0.40/0.57      (![X42 : $i, X43 : $i]:
% 0.40/0.57         (~ (l1_pre_topc @ X42)
% 0.40/0.57          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.40/0.57          | ((k2_pre_topc @ X42 @ (k2_pre_topc @ X42 @ X43))
% 0.40/0.57              = (k2_pre_topc @ X42 @ X43)))),
% 0.40/0.57      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.40/0.57  thf('35', plain,
% 0.40/0.57      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.40/0.57          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.40/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.57  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('37', plain,
% 0.40/0.57      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.40/0.57         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.40/0.57  thf('38', plain,
% 0.40/0.57      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.57      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.40/0.57  thf('39', plain,
% 0.40/0.57      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.57      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.40/0.57  thf('40', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.40/0.57      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.40/0.57  thf('41', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(redefinition_k7_subset_1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.57       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.40/0.57  thf('42', plain,
% 0.40/0.57      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 0.40/0.57          | ((k7_subset_1 @ X38 @ X37 @ X39) = (k4_xboole_0 @ X37 @ X39)))),
% 0.40/0.57      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.40/0.57  thf('43', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.40/0.57           = (k4_xboole_0 @ sk_B @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.40/0.57  thf('44', plain,
% 0.40/0.57      (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.57         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.57      inference('demod', [status(thm)], ['27', '28', '40', '43'])).
% 0.40/0.57  thf('45', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.40/0.57      inference('demod', [status(thm)], ['24', '44'])).
% 0.40/0.57  thf('46', plain, ($false), inference('demod', [status(thm)], ['7', '45'])).
% 0.40/0.57  
% 0.40/0.57  % SZS output end Refutation
% 0.40/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
