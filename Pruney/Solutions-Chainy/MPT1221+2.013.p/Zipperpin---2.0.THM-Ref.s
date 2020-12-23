%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aOOK87Vs42

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:44 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 120 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  517 (1155 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(t29_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tops_1])).

thf('0',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( ( k7_subset_1 @ X3 @ X2 @ X4 )
        = ( k4_xboole_0 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 )
        = ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v4_pre_topc @ X6 @ X7 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k2_struct_0 @ X7 ) @ X6 ) @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['4','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','16'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('18',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('21',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('26',plain,
    ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('29',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('31',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('32',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('35',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 )
        = ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k2_struct_0 @ X7 ) @ X6 ) @ X7 )
      | ( v4_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X1 ) @ X0 ) @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v4_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('43',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','27','28','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.16/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aOOK87Vs42
% 0.17/0.38  % Computer   : n022.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 12:58:56 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.24/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.49  % Solved by: fo/fo7.sh
% 0.24/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.49  % done 59 iterations in 0.015s
% 0.24/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.49  % SZS output start Refutation
% 0.24/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.24/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.49  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.24/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.49  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.24/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.49  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.24/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.24/0.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.24/0.49  thf(t29_tops_1, conjecture,
% 0.24/0.49    (![A:$i]:
% 0.24/0.49     ( ( l1_pre_topc @ A ) =>
% 0.24/0.49       ( ![B:$i]:
% 0.24/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.49           ( ( v4_pre_topc @ B @ A ) <=>
% 0.24/0.49             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.24/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.49    (~( ![A:$i]:
% 0.24/0.49        ( ( l1_pre_topc @ A ) =>
% 0.24/0.49          ( ![B:$i]:
% 0.24/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.49              ( ( v4_pre_topc @ B @ A ) <=>
% 0.24/0.49                ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.24/0.49    inference('cnf.neg', [status(esa)], [t29_tops_1])).
% 0.24/0.49  thf('0', plain,
% 0.24/0.49      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.24/0.49        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('1', plain,
% 0.24/0.49      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.24/0.49       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.49      inference('split', [status(esa)], ['0'])).
% 0.24/0.49  thf(dt_k2_struct_0, axiom,
% 0.24/0.49    (![A:$i]:
% 0.24/0.49     ( ( l1_struct_0 @ A ) =>
% 0.24/0.49       ( m1_subset_1 @
% 0.24/0.49         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.24/0.49  thf('2', plain,
% 0.24/0.49      (![X8 : $i]:
% 0.24/0.49         ((m1_subset_1 @ (k2_struct_0 @ X8) @ 
% 0.24/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.24/0.49          | ~ (l1_struct_0 @ X8))),
% 0.24/0.49      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.24/0.49  thf(redefinition_k7_subset_1, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.49       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.24/0.49  thf('3', plain,
% 0.24/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.24/0.49         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.24/0.49          | ((k7_subset_1 @ X3 @ X2 @ X4) = (k4_xboole_0 @ X2 @ X4)))),
% 0.24/0.49      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.24/0.49  thf('4', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         (~ (l1_struct_0 @ X0)
% 0.24/0.49          | ((k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1)
% 0.24/0.49              = (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1)))),
% 0.24/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.49  thf('5', plain,
% 0.24/0.49      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.24/0.49        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('6', plain,
% 0.24/0.49      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.49      inference('split', [status(esa)], ['5'])).
% 0.24/0.49  thf('7', plain,
% 0.24/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(d6_pre_topc, axiom,
% 0.24/0.49    (![A:$i]:
% 0.24/0.49     ( ( l1_pre_topc @ A ) =>
% 0.24/0.49       ( ![B:$i]:
% 0.24/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.49           ( ( v4_pre_topc @ B @ A ) <=>
% 0.24/0.49             ( v3_pre_topc @
% 0.24/0.49               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 0.24/0.49               A ) ) ) ) ))).
% 0.24/0.49  thf('8', plain,
% 0.24/0.49      (![X6 : $i, X7 : $i]:
% 0.24/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.24/0.49          | ~ (v4_pre_topc @ X6 @ X7)
% 0.24/0.49          | (v3_pre_topc @ 
% 0.24/0.49             (k7_subset_1 @ (u1_struct_0 @ X7) @ (k2_struct_0 @ X7) @ X6) @ X7)
% 0.24/0.49          | ~ (l1_pre_topc @ X7))),
% 0.24/0.49      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.24/0.49  thf('9', plain,
% 0.24/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.49        | (v3_pre_topc @ 
% 0.24/0.49           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.24/0.49           sk_A)
% 0.24/0.49        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.49  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('11', plain,
% 0.24/0.49      (((v3_pre_topc @ 
% 0.24/0.49         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.24/0.49         sk_A)
% 0.24/0.49        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.24/0.49  thf('12', plain,
% 0.24/0.49      (((v3_pre_topc @ 
% 0.24/0.49         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.24/0.49         sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.49      inference('sup-', [status(thm)], ['6', '11'])).
% 0.24/0.49  thf('13', plain,
% 0.24/0.49      ((((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.24/0.49         | ~ (l1_struct_0 @ sk_A))) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.49      inference('sup+', [status(thm)], ['4', '12'])).
% 0.24/0.49  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(dt_l1_pre_topc, axiom,
% 0.24/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.24/0.49  thf('15', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.24/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.24/0.49  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.24/0.49  thf('17', plain,
% 0.24/0.49      (((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.24/0.49         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.49      inference('demod', [status(thm)], ['13', '16'])).
% 0.24/0.49  thf(d3_struct_0, axiom,
% 0.24/0.49    (![A:$i]:
% 0.24/0.49     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.24/0.49  thf('18', plain,
% 0.24/0.49      (![X5 : $i]:
% 0.24/0.49         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.24/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.49  thf('19', plain,
% 0.24/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(d5_subset_1, axiom,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.49       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.24/0.49  thf('20', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         (((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))
% 0.24/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.24/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.24/0.49  thf('21', plain,
% 0.24/0.49      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.24/0.49         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.24/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.24/0.49  thf('22', plain,
% 0.24/0.49      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.24/0.49         <= (~
% 0.24/0.49             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.24/0.49      inference('split', [status(esa)], ['0'])).
% 0.24/0.49  thf('23', plain,
% 0.24/0.49      ((~ (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.24/0.49         <= (~
% 0.24/0.49             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.24/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.24/0.49  thf('24', plain,
% 0.24/0.49      (((~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.24/0.49         | ~ (l1_struct_0 @ sk_A)))
% 0.24/0.49         <= (~
% 0.24/0.49             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.24/0.49      inference('sup-', [status(thm)], ['18', '23'])).
% 0.24/0.49  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.24/0.49  thf('26', plain,
% 0.24/0.49      ((~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.24/0.49         <= (~
% 0.24/0.49             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.24/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.24/0.49  thf('27', plain,
% 0.24/0.49      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.24/0.49       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.49      inference('sup-', [status(thm)], ['17', '26'])).
% 0.24/0.49  thf('28', plain,
% 0.24/0.49      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.24/0.49       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.49      inference('split', [status(esa)], ['5'])).
% 0.24/0.49  thf('29', plain,
% 0.24/0.49      (![X5 : $i]:
% 0.24/0.49         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.24/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.49  thf('30', plain,
% 0.24/0.49      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.24/0.49         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.24/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.24/0.49  thf('31', plain,
% 0.24/0.49      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.24/0.49         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.24/0.49      inference('split', [status(esa)], ['5'])).
% 0.24/0.49  thf('32', plain,
% 0.24/0.49      (((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.24/0.49         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.24/0.49      inference('sup+', [status(thm)], ['30', '31'])).
% 0.24/0.49  thf('33', plain,
% 0.24/0.49      ((((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.24/0.49         | ~ (l1_struct_0 @ sk_A)))
% 0.24/0.49         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.24/0.49      inference('sup+', [status(thm)], ['29', '32'])).
% 0.24/0.49  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.24/0.49  thf('35', plain,
% 0.24/0.49      (((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.24/0.49         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.24/0.49      inference('demod', [status(thm)], ['33', '34'])).
% 0.24/0.49  thf('36', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         (~ (l1_struct_0 @ X0)
% 0.24/0.49          | ((k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1)
% 0.24/0.49              = (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1)))),
% 0.24/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.49  thf('37', plain,
% 0.24/0.49      (![X6 : $i, X7 : $i]:
% 0.24/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.24/0.49          | ~ (v3_pre_topc @ 
% 0.24/0.49               (k7_subset_1 @ (u1_struct_0 @ X7) @ (k2_struct_0 @ X7) @ X6) @ 
% 0.24/0.49               X7)
% 0.24/0.49          | (v4_pre_topc @ X6 @ X7)
% 0.24/0.49          | ~ (l1_pre_topc @ X7))),
% 0.24/0.49      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.24/0.49  thf('38', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         (~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ X1) @ X0) @ X1)
% 0.24/0.49          | ~ (l1_struct_0 @ X1)
% 0.24/0.49          | ~ (l1_pre_topc @ X1)
% 0.24/0.49          | (v4_pre_topc @ X0 @ X1)
% 0.24/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))),
% 0.24/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.24/0.49  thf('39', plain,
% 0.24/0.49      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.49         | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.49         | ~ (l1_pre_topc @ sk_A)
% 0.24/0.49         | ~ (l1_struct_0 @ sk_A)))
% 0.24/0.49         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.24/0.49      inference('sup-', [status(thm)], ['35', '38'])).
% 0.24/0.49  thf('40', plain,
% 0.24/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.24/0.49  thf('43', plain,
% 0.24/0.49      (((v4_pre_topc @ sk_B @ sk_A))
% 0.24/0.49         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.24/0.49      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.24/0.49  thf('44', plain,
% 0.24/0.49      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.49      inference('split', [status(esa)], ['0'])).
% 0.24/0.49  thf('45', plain,
% 0.24/0.49      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.24/0.49       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.24/0.49  thf('46', plain, ($false),
% 0.24/0.49      inference('sat_resolution*', [status(thm)], ['1', '27', '28', '45'])).
% 0.24/0.49  
% 0.24/0.49  % SZS output end Refutation
% 0.24/0.49  
% 0.24/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
