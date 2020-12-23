%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6cu6hEBWcR

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:17 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 102 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  570 (1112 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t72_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t71_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X16 @ ( k1_tops_1 @ X16 @ X15 ) ) @ ( k2_tops_1 @ X16 @ X15 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t71_tops_1])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X3 @ X2 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k2_pre_topc @ X14 @ X13 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 @ ( k2_tops_1 @ X14 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k2_tops_1 @ X12 @ X11 )
        = ( k2_tops_1 @ X12 @ ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( ( k1_tops_1 @ X8 @ X7 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k2_pre_topc @ X8 @ ( k3_subset_1 @ ( u1_struct_0 @ X8 ) @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('31',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28','31'])).

thf('33',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','24','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k2_tops_1 @ X12 @ X11 )
        = ( k2_tops_1 @ X12 @ ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf('39',plain,
    ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6','33','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6cu6hEBWcR
% 0.11/0.32  % Computer   : n023.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 13:06:36 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.32  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.17/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.17/0.57  % Solved by: fo/fo7.sh
% 0.17/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.17/0.57  % done 107 iterations in 0.135s
% 0.17/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.17/0.57  % SZS output start Refutation
% 0.17/0.57  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.17/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.17/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.17/0.57  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.17/0.57  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.17/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.17/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.17/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.17/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.17/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.17/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.17/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.17/0.57  thf(t72_tops_1, conjecture,
% 0.17/0.57    (![A:$i]:
% 0.17/0.57     ( ( l1_pre_topc @ A ) =>
% 0.17/0.57       ( ![B:$i]:
% 0.17/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.17/0.57           ( r1_tarski @
% 0.17/0.57             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 0.17/0.57             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.17/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.17/0.57    (~( ![A:$i]:
% 0.17/0.57        ( ( l1_pre_topc @ A ) =>
% 0.17/0.57          ( ![B:$i]:
% 0.17/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.17/0.57              ( r1_tarski @
% 0.17/0.57                ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 0.17/0.57                ( k2_tops_1 @ A @ B ) ) ) ) ) )),
% 0.17/0.57    inference('cnf.neg', [status(esa)], [t72_tops_1])).
% 0.17/0.57  thf('0', plain,
% 0.17/0.57      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.17/0.57          (k2_tops_1 @ sk_A @ sk_B))),
% 0.17/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.57  thf('1', plain,
% 0.17/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.57  thf(dt_k3_subset_1, axiom,
% 0.17/0.57    (![A:$i,B:$i]:
% 0.17/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.17/0.57       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.17/0.57  thf('2', plain,
% 0.17/0.57      (![X0 : $i, X1 : $i]:
% 0.17/0.57         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.17/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.17/0.57      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.17/0.57  thf('3', plain,
% 0.17/0.57      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.17/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.17/0.57  thf(t71_tops_1, axiom,
% 0.17/0.57    (![A:$i]:
% 0.17/0.57     ( ( l1_pre_topc @ A ) =>
% 0.17/0.57       ( ![B:$i]:
% 0.17/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.17/0.57           ( r1_tarski @
% 0.17/0.57             ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.17/0.57  thf('4', plain,
% 0.17/0.57      (![X15 : $i, X16 : $i]:
% 0.17/0.57         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.17/0.57          | (r1_tarski @ (k2_tops_1 @ X16 @ (k1_tops_1 @ X16 @ X15)) @ 
% 0.17/0.57             (k2_tops_1 @ X16 @ X15))
% 0.17/0.57          | ~ (l1_pre_topc @ X16))),
% 0.17/0.57      inference('cnf', [status(esa)], [t71_tops_1])).
% 0.17/0.57  thf('5', plain,
% 0.17/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.17/0.57        | (r1_tarski @ 
% 0.17/0.57           (k2_tops_1 @ sk_A @ 
% 0.17/0.57            (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 0.17/0.57           (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.17/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.17/0.57  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.57  thf('7', plain,
% 0.17/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.57  thf(dt_k2_tops_1, axiom,
% 0.17/0.57    (![A:$i,B:$i]:
% 0.17/0.57     ( ( ( l1_pre_topc @ A ) & 
% 0.17/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.17/0.57       ( m1_subset_1 @
% 0.17/0.57         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.17/0.57  thf('8', plain,
% 0.17/0.57      (![X9 : $i, X10 : $i]:
% 0.17/0.57         (~ (l1_pre_topc @ X9)
% 0.17/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.17/0.57          | (m1_subset_1 @ (k2_tops_1 @ X9 @ X10) @ 
% 0.17/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.17/0.57      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.17/0.57  thf('9', plain,
% 0.17/0.57      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.17/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.17/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.17/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.17/0.57  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.57  thf('11', plain,
% 0.17/0.57      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.17/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.17/0.57  thf('12', plain,
% 0.17/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.57  thf(dt_k4_subset_1, axiom,
% 0.17/0.57    (![A:$i,B:$i,C:$i]:
% 0.17/0.57     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.17/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.17/0.57       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.17/0.57  thf('13', plain,
% 0.17/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.17/0.57         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.17/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3))
% 0.17/0.57          | (m1_subset_1 @ (k4_subset_1 @ X3 @ X2 @ X4) @ (k1_zfmisc_1 @ X3)))),
% 0.17/0.57      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.17/0.57  thf('14', plain,
% 0.17/0.57      (![X0 : $i]:
% 0.17/0.57         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.17/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.17/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.17/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.17/0.57  thf('15', plain,
% 0.17/0.57      ((m1_subset_1 @ 
% 0.17/0.57        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.17/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.57      inference('sup-', [status(thm)], ['11', '14'])).
% 0.17/0.57  thf('16', plain,
% 0.17/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.57  thf(t65_tops_1, axiom,
% 0.17/0.57    (![A:$i]:
% 0.17/0.57     ( ( l1_pre_topc @ A ) =>
% 0.17/0.57       ( ![B:$i]:
% 0.17/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.17/0.57           ( ( k2_pre_topc @ A @ B ) =
% 0.17/0.57             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.17/0.57  thf('17', plain,
% 0.17/0.57      (![X13 : $i, X14 : $i]:
% 0.17/0.57         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.17/0.57          | ((k2_pre_topc @ X14 @ X13)
% 0.17/0.57              = (k4_subset_1 @ (u1_struct_0 @ X14) @ X13 @ 
% 0.17/0.57                 (k2_tops_1 @ X14 @ X13)))
% 0.17/0.57          | ~ (l1_pre_topc @ X14))),
% 0.17/0.57      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.17/0.57  thf('18', plain,
% 0.17/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.17/0.57        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.17/0.57            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.17/0.57               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.17/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.17/0.57  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.57  thf('20', plain,
% 0.17/0.57      (((k2_pre_topc @ sk_A @ sk_B)
% 0.17/0.57         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.17/0.57            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.17/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.17/0.57  thf('21', plain,
% 0.17/0.57      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.17/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.57      inference('demod', [status(thm)], ['15', '20'])).
% 0.17/0.57  thf(t62_tops_1, axiom,
% 0.17/0.57    (![A:$i]:
% 0.17/0.57     ( ( l1_pre_topc @ A ) =>
% 0.17/0.57       ( ![B:$i]:
% 0.17/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.17/0.57           ( ( k2_tops_1 @ A @ B ) =
% 0.17/0.57             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.17/0.57  thf('22', plain,
% 0.17/0.57      (![X11 : $i, X12 : $i]:
% 0.17/0.57         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.17/0.57          | ((k2_tops_1 @ X12 @ X11)
% 0.17/0.57              = (k2_tops_1 @ X12 @ (k3_subset_1 @ (u1_struct_0 @ X12) @ X11)))
% 0.17/0.57          | ~ (l1_pre_topc @ X12))),
% 0.17/0.57      inference('cnf', [status(esa)], [t62_tops_1])).
% 0.17/0.57  thf('23', plain,
% 0.17/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.17/0.57        | ((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.17/0.57            = (k2_tops_1 @ sk_A @ 
% 0.17/0.57               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.17/0.57                (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.17/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.17/0.57  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.57  thf('25', plain,
% 0.17/0.57      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.17/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.17/0.57  thf(d1_tops_1, axiom,
% 0.17/0.57    (![A:$i]:
% 0.17/0.57     ( ( l1_pre_topc @ A ) =>
% 0.17/0.57       ( ![B:$i]:
% 0.17/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.17/0.57           ( ( k1_tops_1 @ A @ B ) =
% 0.17/0.57             ( k3_subset_1 @
% 0.17/0.57               ( u1_struct_0 @ A ) @ 
% 0.17/0.57               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.17/0.57  thf('26', plain,
% 0.17/0.57      (![X7 : $i, X8 : $i]:
% 0.17/0.57         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.17/0.57          | ((k1_tops_1 @ X8 @ X7)
% 0.17/0.57              = (k3_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.17/0.57                 (k2_pre_topc @ X8 @ (k3_subset_1 @ (u1_struct_0 @ X8) @ X7))))
% 0.17/0.57          | ~ (l1_pre_topc @ X8))),
% 0.17/0.57      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.17/0.57  thf('27', plain,
% 0.17/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.17/0.57        | ((k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.17/0.57            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.17/0.57               (k2_pre_topc @ sk_A @ 
% 0.17/0.57                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.17/0.57                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 0.17/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.17/0.57  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.57  thf('29', plain,
% 0.17/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.57  thf(involutiveness_k3_subset_1, axiom,
% 0.17/0.57    (![A:$i,B:$i]:
% 0.17/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.17/0.57       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.17/0.57  thf('30', plain,
% 0.17/0.57      (![X5 : $i, X6 : $i]:
% 0.17/0.57         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 0.17/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.17/0.57      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.17/0.57  thf('31', plain,
% 0.17/0.57      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.17/0.57         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.17/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.17/0.57  thf('32', plain,
% 0.17/0.57      (((k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.17/0.57         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.17/0.57      inference('demod', [status(thm)], ['27', '28', '31'])).
% 0.17/0.57  thf('33', plain,
% 0.17/0.57      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.17/0.57         = (k2_tops_1 @ sk_A @ 
% 0.17/0.57            (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.17/0.57      inference('demod', [status(thm)], ['23', '24', '32'])).
% 0.17/0.57  thf('34', plain,
% 0.17/0.57      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.17/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.17/0.57  thf('35', plain,
% 0.17/0.57      (![X11 : $i, X12 : $i]:
% 0.17/0.57         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.17/0.57          | ((k2_tops_1 @ X12 @ X11)
% 0.17/0.57              = (k2_tops_1 @ X12 @ (k3_subset_1 @ (u1_struct_0 @ X12) @ X11)))
% 0.17/0.57          | ~ (l1_pre_topc @ X12))),
% 0.17/0.57      inference('cnf', [status(esa)], [t62_tops_1])).
% 0.17/0.57  thf('36', plain,
% 0.17/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.17/0.57        | ((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.17/0.57            = (k2_tops_1 @ sk_A @ 
% 0.17/0.57               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.17/0.57                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.17/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.17/0.57  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.57  thf('38', plain,
% 0.17/0.57      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.17/0.57         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.17/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.17/0.57  thf('39', plain,
% 0.17/0.57      (((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.17/0.57         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.17/0.57      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.17/0.57  thf('40', plain,
% 0.17/0.57      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.17/0.57        (k2_tops_1 @ sk_A @ sk_B))),
% 0.17/0.57      inference('demod', [status(thm)], ['5', '6', '33', '39'])).
% 0.17/0.57  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.17/0.57  
% 0.17/0.57  % SZS output end Refutation
% 0.17/0.57  
% 0.17/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
