%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GhZGu6S7ew

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 100 expanded)
%              Number of leaves         :   28 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  520 (1660 expanded)
%              Number of equality atoms :   18 (  48 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k1_tarski @ X3 ) )
        = X2 )
      | ( r2_hidden @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('3',plain,(
    sk_B
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
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

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( v2_waybel_0 @ X9 @ ( k3_yellow_1 @ ( k2_struct_0 @ X10 ) ) )
      | ~ ( v13_waybel_0 @ X9 @ ( k3_yellow_1 @ ( k2_struct_0 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X10 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X10 ) ) ) @ X9 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X10 @ ( k3_yellow19 @ X10 @ ( k2_struct_0 @ X10 ) @ X9 ) ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( ( k7_subset_1 @ X5 @ X4 @ X6 )
        = ( k4_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    sk_B
 != ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','17'])).

thf('19',plain,
    ( ( sk_B != sk_B )
    | ( r2_hidden @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','18'])).

thf('20',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
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

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( v1_subset_1 @ X11 @ ( u1_struct_0 @ ( k3_yellow_1 @ X12 ) ) )
      | ~ ( v2_waybel_0 @ X11 @ ( k3_yellow_1 @ X12 ) )
      | ~ ( v13_waybel_0 @ X11 @ ( k3_yellow_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X12 ) ) ) )
      | ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( v1_xboole_0 @ X13 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(d1_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( v2_struct_0 @ A )
      <=> ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('36',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_struct_0])).

thf('37',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GhZGu6S7ew
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:23:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 41 iterations in 0.023s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.19/0.45  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.19/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.45  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.19/0.45  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.45  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.45  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.19/0.45  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.19/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.45  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.45  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.19/0.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.45  thf(t15_yellow19, conjecture,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.45       ( ![B:$i]:
% 0.19/0.45         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.45             ( v1_subset_1 @
% 0.19/0.45               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.19/0.45             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.45             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.45             ( m1_subset_1 @
% 0.19/0.45               B @ 
% 0.19/0.45               ( k1_zfmisc_1 @
% 0.19/0.45                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.19/0.45           ( ( B ) =
% 0.19/0.45             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i]:
% 0.19/0.45        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.45          ( ![B:$i]:
% 0.19/0.45            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.45                ( v1_subset_1 @
% 0.19/0.45                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.19/0.45                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.45                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.45                ( m1_subset_1 @
% 0.19/0.45                  B @ 
% 0.19/0.45                  ( k1_zfmisc_1 @
% 0.19/0.45                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.19/0.45              ( ( B ) =
% 0.19/0.45                ( k2_yellow19 @
% 0.19/0.45                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.19/0.45  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(d3_struct_0, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      (![X7 : $i]:
% 0.19/0.45         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.19/0.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.45  thf(t65_zfmisc_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.19/0.45       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.19/0.45  thf('2', plain,
% 0.19/0.45      (![X2 : $i, X3 : $i]:
% 0.19/0.45         (((k4_xboole_0 @ X2 @ (k1_tarski @ X3)) = (X2))
% 0.19/0.45          | (r2_hidden @ X3 @ X2))),
% 0.19/0.45      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.19/0.45  thf('3', plain,
% 0.19/0.45      (((sk_B)
% 0.19/0.45         != (k2_yellow19 @ sk_A @ 
% 0.19/0.45             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('4', plain,
% 0.19/0.45      ((m1_subset_1 @ sk_B @ 
% 0.19/0.45        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t14_yellow19, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.45       ( ![B:$i]:
% 0.19/0.45         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.45             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.45             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.45             ( m1_subset_1 @
% 0.19/0.45               B @ 
% 0.19/0.45               ( k1_zfmisc_1 @
% 0.19/0.45                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.19/0.45           ( ( k7_subset_1 @
% 0.19/0.45               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.19/0.45               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.19/0.45             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.19/0.45  thf('5', plain,
% 0.19/0.45      (![X9 : $i, X10 : $i]:
% 0.19/0.45         ((v1_xboole_0 @ X9)
% 0.19/0.45          | ~ (v2_waybel_0 @ X9 @ (k3_yellow_1 @ (k2_struct_0 @ X10)))
% 0.19/0.45          | ~ (v13_waybel_0 @ X9 @ (k3_yellow_1 @ (k2_struct_0 @ X10)))
% 0.19/0.45          | ~ (m1_subset_1 @ X9 @ 
% 0.19/0.45               (k1_zfmisc_1 @ 
% 0.19/0.45                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X10)))))
% 0.19/0.45          | ((k7_subset_1 @ 
% 0.19/0.45              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X10))) @ X9 @ 
% 0.19/0.45              (k1_tarski @ k1_xboole_0))
% 0.19/0.45              = (k2_yellow19 @ X10 @ 
% 0.19/0.45                 (k3_yellow19 @ X10 @ (k2_struct_0 @ X10) @ X9)))
% 0.19/0.45          | ~ (l1_struct_0 @ X10)
% 0.19/0.45          | (v2_struct_0 @ X10))),
% 0.19/0.45      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.19/0.45  thf('6', plain,
% 0.19/0.45      (((v2_struct_0 @ sk_A)
% 0.19/0.45        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.45        | ((k7_subset_1 @ 
% 0.19/0.45            (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))) @ sk_B @ 
% 0.19/0.45            (k1_tarski @ k1_xboole_0))
% 0.19/0.45            = (k2_yellow19 @ sk_A @ 
% 0.19/0.45               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.45        | ~ (v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.19/0.45        | ~ (v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.19/0.45        | (v1_xboole_0 @ sk_B))),
% 0.19/0.45      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.45  thf('7', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('8', plain,
% 0.19/0.45      ((m1_subset_1 @ sk_B @ 
% 0.19/0.45        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(redefinition_k7_subset_1, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i]:
% 0.19/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.45       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.19/0.45  thf('9', plain,
% 0.19/0.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.45         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.19/0.45          | ((k7_subset_1 @ X5 @ X4 @ X6) = (k4_xboole_0 @ X4 @ X6)))),
% 0.19/0.45      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.19/0.45  thf('10', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         ((k7_subset_1 @ 
% 0.19/0.45           (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))) @ sk_B @ X0)
% 0.19/0.45           = (k4_xboole_0 @ sk_B @ X0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.45  thf('11', plain,
% 0.19/0.45      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('12', plain,
% 0.19/0.45      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('13', plain,
% 0.19/0.45      (((v2_struct_0 @ sk_A)
% 0.19/0.45        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.19/0.45            = (k2_yellow19 @ sk_A @ 
% 0.19/0.45               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.45        | (v1_xboole_0 @ sk_B))),
% 0.19/0.45      inference('demod', [status(thm)], ['6', '7', '10', '11', '12'])).
% 0.19/0.45  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('15', plain,
% 0.19/0.45      (((v1_xboole_0 @ sk_B)
% 0.19/0.45        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.19/0.45            = (k2_yellow19 @ sk_A @ 
% 0.19/0.45               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.19/0.45      inference('clc', [status(thm)], ['13', '14'])).
% 0.19/0.45  thf('16', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('17', plain,
% 0.19/0.45      (((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.19/0.45         = (k2_yellow19 @ sk_A @ 
% 0.19/0.45            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.45      inference('clc', [status(thm)], ['15', '16'])).
% 0.19/0.45  thf('18', plain,
% 0.19/0.45      (((sk_B) != (k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0)))),
% 0.19/0.45      inference('demod', [status(thm)], ['3', '17'])).
% 0.19/0.45  thf('19', plain, ((((sk_B) != (sk_B)) | (r2_hidden @ k1_xboole_0 @ sk_B))),
% 0.19/0.45      inference('sup-', [status(thm)], ['2', '18'])).
% 0.19/0.45  thf('20', plain, ((r2_hidden @ k1_xboole_0 @ sk_B)),
% 0.19/0.45      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.45  thf('21', plain,
% 0.19/0.45      ((m1_subset_1 @ sk_B @ 
% 0.19/0.45        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t2_yellow19, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.45       ( ![B:$i]:
% 0.19/0.45         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.45             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.19/0.45             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.19/0.45             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.19/0.45             ( m1_subset_1 @
% 0.19/0.45               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.19/0.45           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.19/0.45  thf('22', plain,
% 0.19/0.45      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.45         ((v1_xboole_0 @ X11)
% 0.19/0.45          | ~ (v1_subset_1 @ X11 @ (u1_struct_0 @ (k3_yellow_1 @ X12)))
% 0.19/0.45          | ~ (v2_waybel_0 @ X11 @ (k3_yellow_1 @ X12))
% 0.19/0.45          | ~ (v13_waybel_0 @ X11 @ (k3_yellow_1 @ X12))
% 0.19/0.45          | ~ (m1_subset_1 @ X11 @ 
% 0.19/0.45               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X12))))
% 0.19/0.45          | ~ (r2_hidden @ X13 @ X11)
% 0.19/0.45          | ~ (v1_xboole_0 @ X13)
% 0.19/0.45          | (v1_xboole_0 @ X12))),
% 0.19/0.45      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.19/0.45  thf('23', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.45          | ~ (v1_xboole_0 @ X0)
% 0.19/0.45          | ~ (r2_hidden @ X0 @ sk_B)
% 0.19/0.45          | ~ (v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.19/0.45          | ~ (v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.19/0.45          | ~ (v1_subset_1 @ sk_B @ 
% 0.19/0.45               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.19/0.45          | (v1_xboole_0 @ sk_B))),
% 0.19/0.45      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.45  thf('24', plain,
% 0.19/0.45      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('25', plain,
% 0.19/0.45      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('26', plain,
% 0.19/0.45      ((v1_subset_1 @ sk_B @ 
% 0.19/0.45        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('27', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.45          | ~ (v1_xboole_0 @ X0)
% 0.19/0.45          | ~ (r2_hidden @ X0 @ sk_B)
% 0.19/0.45          | (v1_xboole_0 @ sk_B))),
% 0.19/0.45      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.19/0.45  thf('28', plain,
% 0.19/0.45      (((v1_xboole_0 @ sk_B)
% 0.19/0.45        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.45        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['20', '27'])).
% 0.19/0.45  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.45  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.45  thf('30', plain,
% 0.19/0.45      (((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.19/0.45      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.45  thf('31', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('32', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.19/0.45      inference('clc', [status(thm)], ['30', '31'])).
% 0.19/0.45  thf('33', plain,
% 0.19/0.45      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.45      inference('sup+', [status(thm)], ['1', '32'])).
% 0.19/0.45  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('35', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.19/0.45      inference('demod', [status(thm)], ['33', '34'])).
% 0.19/0.45  thf(d1_struct_0, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( l1_struct_0 @ A ) =>
% 0.19/0.45       ( ( v2_struct_0 @ A ) <=> ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.45  thf('36', plain,
% 0.19/0.45      (![X8 : $i]:
% 0.19/0.45         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.19/0.45          | (v2_struct_0 @ X8)
% 0.19/0.45          | ~ (l1_struct_0 @ X8))),
% 0.19/0.45      inference('cnf', [status(esa)], [d1_struct_0])).
% 0.19/0.45  thf('37', plain, ((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.19/0.45      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.45  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('39', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.45      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.45  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
