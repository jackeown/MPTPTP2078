%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VTxpFtSHnd

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 (  99 expanded)
%              Number of leaves         :   28 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  559 (1628 expanded)
%              Number of equality atoms :   21 (  50 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t15_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ( B
            = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
              & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
           => ( B
              = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_yellow19])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X5 @ ( k1_tarski @ X6 ) )
        = X5 )
      | ( r2_hidden @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        = X0 )
      | ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    sk_B
 != ( k2_yellow19 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ ( k1_tarski @ k1_xboole_0 ) )
            = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( v2_waybel_0 @ X16 @ ( k3_yellow_1 @ ( k2_struct_0 @ X17 ) ) )
      | ~ ( v13_waybel_0 @ X16 @ ( k3_yellow_1 @ ( k2_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X17 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X17 ) ) ) @ X16 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X17 @ ( k3_yellow19 @ X17 @ ( k2_struct_0 @ X17 ) @ X16 ) ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('7',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( v2_waybel_0 @ X16 @ ( k3_yellow_1 @ ( k2_struct_0 @ X17 ) ) )
      | ~ ( v13_waybel_0 @ X16 @ ( k3_yellow_1 @ ( k2_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X17 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X17 ) ) ) @ X16 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X17 @ ( k3_yellow19 @ X17 @ ( k2_struct_0 @ X17 ) @ X16 ) ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A_1 )
    | ~ ( l1_struct_0 @ sk_A_1 )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) @ sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k7_subset_1 @ X11 @ X10 @ X12 )
        = ( k4_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A_1 )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    sk_B
 != ( k4_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','20'])).

thf('22',plain,
    ( ( sk_B != sk_B )
    | ( r2_hidden @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','21'])).

thf('23',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_yellow19,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
         => ! [C: $i] :
              ~ ( ( r2_hidden @ C @ B )
                & ( v1_xboole_0 @ C ) ) ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_subset_1 @ X18 @ ( u1_struct_0 @ ( k3_yellow_1 @ X19 ) ) )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_yellow_1 @ X19 ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_yellow_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X19 ) ) ) )
      | ~ ( r2_hidden @ X20 @ X18 )
      | ~ ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('36',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A_1 )
    | ~ ( l1_struct_0 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_struct_0 @ sk_A_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VTxpFtSHnd
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:45:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 61 iterations in 0.034s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.21/0.49  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.49  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(t15_yellow19, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.49             ( v1_subset_1 @
% 0.21/0.49               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.49             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.49             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.49             ( m1_subset_1 @
% 0.21/0.49               B @ 
% 0.21/0.49               ( k1_zfmisc_1 @
% 0.21/0.49                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.49           ( ( B ) =
% 0.21/0.49             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.49                ( v1_subset_1 @
% 0.21/0.49                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.49                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.49                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.49                ( m1_subset_1 @
% 0.21/0.49                  B @ 
% 0.21/0.49                  ( k1_zfmisc_1 @
% 0.21/0.49                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.49              ( ( B ) =
% 0.21/0.49                ( k2_yellow19 @
% 0.21/0.49                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.21/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_A_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t1_zfmisc_1, axiom,
% 0.21/0.49    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.21/0.49  thf('1', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.21/0.49  thf(t65_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.21/0.49       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ X5 @ (k1_tarski @ X6)) = (X5))
% 0.21/0.49          | (r2_hidden @ X6 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0)) = (X0))
% 0.21/0.49          | (r2_hidden @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((sk_B)
% 0.21/0.49         != (k2_yellow19 @ sk_A_1 @ 
% 0.21/0.49             (k3_yellow19 @ sk_A_1 @ (k2_struct_0 @ sk_A_1) @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A_1)))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t14_yellow19, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.49             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.49             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.49             ( m1_subset_1 @
% 0.21/0.49               B @ 
% 0.21/0.49               ( k1_zfmisc_1 @
% 0.21/0.49                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.49           ( ( k7_subset_1 @
% 0.21/0.49               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.21/0.49               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.21/0.49             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X16)
% 0.21/0.49          | ~ (v2_waybel_0 @ X16 @ (k3_yellow_1 @ (k2_struct_0 @ X17)))
% 0.21/0.49          | ~ (v13_waybel_0 @ X16 @ (k3_yellow_1 @ (k2_struct_0 @ X17)))
% 0.21/0.49          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.49               (k1_zfmisc_1 @ 
% 0.21/0.49                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X17)))))
% 0.21/0.49          | ((k7_subset_1 @ 
% 0.21/0.49              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X17))) @ X16 @ 
% 0.21/0.49              (k1_tarski @ k1_xboole_0))
% 0.21/0.49              = (k2_yellow19 @ X17 @ 
% 0.21/0.49                 (k3_yellow19 @ X17 @ (k2_struct_0 @ X17) @ X16)))
% 0.21/0.49          | ~ (l1_struct_0 @ X17)
% 0.21/0.49          | (v2_struct_0 @ X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.21/0.49  thf('7', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X16)
% 0.21/0.49          | ~ (v2_waybel_0 @ X16 @ (k3_yellow_1 @ (k2_struct_0 @ X17)))
% 0.21/0.49          | ~ (v13_waybel_0 @ X16 @ (k3_yellow_1 @ (k2_struct_0 @ X17)))
% 0.21/0.49          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.49               (k1_zfmisc_1 @ 
% 0.21/0.49                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X17)))))
% 0.21/0.49          | ((k7_subset_1 @ 
% 0.21/0.49              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X17))) @ X16 @ 
% 0.21/0.49              (k1_zfmisc_1 @ k1_xboole_0))
% 0.21/0.49              = (k2_yellow19 @ X17 @ 
% 0.21/0.49                 (k3_yellow19 @ X17 @ (k2_struct_0 @ X17) @ X16)))
% 0.21/0.49          | ~ (l1_struct_0 @ X17)
% 0.21/0.49          | (v2_struct_0 @ X17))),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A_1)
% 0.21/0.49        | ~ (l1_struct_0 @ sk_A_1)
% 0.21/0.49        | ((k7_subset_1 @ 
% 0.21/0.49            (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A_1))) @ sk_B @ 
% 0.21/0.49            (k1_zfmisc_1 @ k1_xboole_0))
% 0.21/0.49            = (k2_yellow19 @ sk_A_1 @ 
% 0.21/0.49               (k3_yellow19 @ sk_A_1 @ (k2_struct_0 @ sk_A_1) @ sk_B)))
% 0.21/0.49        | ~ (v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A_1)))
% 0.21/0.49        | ~ (v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A_1)))
% 0.21/0.49        | (v1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.49  thf('10', plain, ((l1_struct_0 @ sk_A_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A_1)))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.21/0.49          | ((k7_subset_1 @ X11 @ X10 @ X12) = (k4_xboole_0 @ X10 @ X12)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k7_subset_1 @ 
% 0.21/0.49           (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A_1))) @ sk_B @ X0)
% 0.21/0.49           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A_1)
% 0.21/0.49        | ((k4_xboole_0 @ sk_B @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.21/0.49            = (k2_yellow19 @ sk_A_1 @ 
% 0.21/0.49               (k3_yellow19 @ sk_A_1 @ (k2_struct_0 @ sk_A_1) @ sk_B)))
% 0.21/0.49        | (v1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10', '13', '14', '15'])).
% 0.21/0.49  thf('17', plain, (~ (v2_struct_0 @ sk_A_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (((v1_xboole_0 @ sk_B)
% 0.21/0.49        | ((k4_xboole_0 @ sk_B @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.21/0.49            = (k2_yellow19 @ sk_A_1 @ 
% 0.21/0.49               (k3_yellow19 @ sk_A_1 @ (k2_struct_0 @ sk_A_1) @ sk_B))))),
% 0.21/0.49      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (((k4_xboole_0 @ sk_B @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.21/0.49         = (k2_yellow19 @ sk_A_1 @ 
% 0.21/0.49            (k3_yellow19 @ sk_A_1 @ (k2_struct_0 @ sk_A_1) @ sk_B)))),
% 0.21/0.49      inference('clc', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (((sk_B) != (k4_xboole_0 @ sk_B @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '20'])).
% 0.21/0.49  thf('22', plain, ((((sk_B) != (sk_B)) | (r2_hidden @ k1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '21'])).
% 0.21/0.49  thf('23', plain, ((r2_hidden @ k1_xboole_0 @ sk_B)),
% 0.21/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A_1)))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t2_yellow19, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.49             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.21/0.49             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.49             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.49             ( m1_subset_1 @
% 0.21/0.49               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.21/0.49           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X18)
% 0.21/0.49          | ~ (v1_subset_1 @ X18 @ (u1_struct_0 @ (k3_yellow_1 @ X19)))
% 0.21/0.49          | ~ (v2_waybel_0 @ X18 @ (k3_yellow_1 @ X19))
% 0.21/0.49          | ~ (v13_waybel_0 @ X18 @ (k3_yellow_1 @ X19))
% 0.21/0.49          | ~ (m1_subset_1 @ X18 @ 
% 0.21/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X19))))
% 0.21/0.49          | ~ (r2_hidden @ X20 @ X18)
% 0.21/0.49          | ~ (v1_xboole_0 @ X20)
% 0.21/0.49          | (v1_xboole_0 @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (k2_struct_0 @ sk_A_1))
% 0.21/0.49          | ~ (v1_xboole_0 @ X0)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.49          | ~ (v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A_1)))
% 0.21/0.49          | ~ (v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A_1)))
% 0.21/0.49          | ~ (v1_subset_1 @ sk_B @ 
% 0.21/0.49               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A_1))))
% 0.21/0.49          | (v1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      ((v1_subset_1 @ sk_B @ 
% 0.21/0.49        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A_1))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (k2_struct_0 @ sk_A_1))
% 0.21/0.49          | ~ (v1_xboole_0 @ X0)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.49          | (v1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (((v1_xboole_0 @ sk_B)
% 0.21/0.49        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.49        | (v1_xboole_0 @ (k2_struct_0 @ sk_A_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '30'])).
% 0.21/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.49  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('34', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A_1))),
% 0.21/0.49      inference('clc', [status(thm)], ['33', '34'])).
% 0.21/0.49  thf(fc5_struct_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X15 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (k2_struct_0 @ X15))
% 0.21/0.49          | ~ (l1_struct_0 @ X15)
% 0.21/0.49          | (v2_struct_0 @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.21/0.49  thf('37', plain, (((v2_struct_0 @ sk_A_1) | ~ (l1_struct_0 @ sk_A_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.49  thf('38', plain, ((l1_struct_0 @ sk_A_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('39', plain, ((v2_struct_0 @ sk_A_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
