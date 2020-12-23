%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vipCtt92S3

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 117 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  523 (1078 expanded)
%              Number of equality atoms :   11 (  27 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X4: $i] :
      ( ( k6_subset_1 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t29_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_yellow_6])).

thf('3',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ~ ( r1_waybel_0 @ A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( r1_waybel_0 @ X19 @ X18 @ ( k6_subset_1 @ ( u1_struct_0 @ X19 ) @ X20 ) )
      | ( r2_waybel_0 @ X19 @ X18 @ X20 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['12','13'])).

thf(t8_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i,D: $i] :
              ( ( r1_tarski @ C @ D )
             => ( ( ( r1_waybel_0 @ A @ B @ C )
                 => ( r1_waybel_0 @ A @ B @ D ) )
                & ( ( r2_waybel_0 @ A @ B @ C )
                 => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( l1_waybel_0 @ X22 @ X23 )
      | ~ ( r2_waybel_0 @ X23 @ X22 @ X24 )
      | ( r2_waybel_0 @ X23 @ X22 @ X25 )
      | ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_waybel_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X4: $i] :
      ( ( k6_subset_1 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X5 @ X7 ) @ X6 )
       != ( k2_tarski @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( ( k6_subset_1 @ ( k2_tarski @ X5 @ X7 ) @ X6 )
       != ( k2_tarski @ X5 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
       != ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['16','17','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('32',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( sk_B @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(d12_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                 => ? [E: $i] :
                      ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C )
                      & ( r1_orders_2 @ B @ D @ E )
                      & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X12: $i,X13: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( r2_waybel_0 @ X13 @ X12 @ X16 )
      | ( r2_hidden @ ( k2_waybel_0 @ X13 @ X12 @ ( sk_E @ X17 @ X16 @ X12 @ X13 ) ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('44',plain,(
    $false ),
    inference('sup-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vipCtt92S3
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:36:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 50 iterations in 0.029s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.50  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.21/0.50  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.21/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.50  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.50  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.50  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(t3_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.50  thf('0', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.50  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i]:
% 0.21/0.50         ((k6_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.50  thf('2', plain, (![X4 : $i]: ((k6_subset_1 @ X4 @ k1_xboole_0) = (X4))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf(t29_yellow_6, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.50             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.50                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.21/0.50  thf('3', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t10_waybel_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.21/0.50               ( ~( r1_waybel_0 @
% 0.21/0.50                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X18)
% 0.21/0.50          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.50          | (r1_waybel_0 @ X19 @ X18 @ 
% 0.21/0.50             (k6_subset_1 @ (u1_struct_0 @ X19) @ X20))
% 0.21/0.50          | (r2_waybel_0 @ X19 @ X18 @ X20)
% 0.21/0.50          | ~ (l1_struct_0 @ X19)
% 0.21/0.50          | (v2_struct_0 @ X19))),
% 0.21/0.50      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.21/0.50          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.21/0.50          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (((r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (v2_struct_0 @ sk_B_1)
% 0.21/0.50        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup+', [status(thm)], ['2', '7'])).
% 0.21/0.50  thf('9', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.21/0.50        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0))),
% 0.21/0.50      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain, ((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)),
% 0.21/0.50      inference('clc', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf(t8_waybel_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i,D:$i]:
% 0.21/0.50             ( ( r1_tarski @ C @ D ) =>
% 0.21/0.50               ( ( ( r1_waybel_0 @ A @ B @ C ) => ( r1_waybel_0 @ A @ B @ D ) ) & 
% 0.21/0.50                 ( ( r2_waybel_0 @ A @ B @ C ) => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X22)
% 0.21/0.50          | ~ (l1_waybel_0 @ X22 @ X23)
% 0.21/0.50          | ~ (r2_waybel_0 @ X23 @ X22 @ X24)
% 0.21/0.50          | (r2_waybel_0 @ X23 @ X22 @ X25)
% 0.21/0.50          | ~ (r1_tarski @ X24 @ X25)
% 0.21/0.50          | ~ (l1_struct_0 @ X23)
% 0.21/0.50          | (v2_struct_0 @ X23))),
% 0.21/0.50      inference('cnf', [status(esa)], [t8_waybel_0])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50          | ~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.21/0.50          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d3_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('19', plain, (![X4 : $i]: ((k6_subset_1 @ X4 @ k1_xboole_0) = (X4))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf(t72_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.50       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.50          | ((k4_xboole_0 @ (k2_tarski @ X5 @ X7) @ X6)
% 0.21/0.50              != (k2_tarski @ X5 @ X7)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i]:
% 0.21/0.50         ((k6_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.50          | ((k6_subset_1 @ (k2_tarski @ X5 @ X7) @ X6)
% 0.21/0.50              != (k2_tarski @ X5 @ X7)))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k2_tarski @ X1 @ X0) != (k2_tarski @ X1 @ X0))
% 0.21/0.50          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '22'])).
% 0.21/0.50  thf('24', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.50  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '24'])).
% 0.21/0.50  thf('26', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '17', '25', '26'])).
% 0.21/0.50  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0))),
% 0.21/0.50      inference('clc', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('31', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 0.21/0.50      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf(existence_m1_subset_1, axiom,
% 0.21/0.50    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.21/0.50  thf('32', plain, (![X9 : $i]: (m1_subset_1 @ (sk_B @ X9) @ X9)),
% 0.21/0.50      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.21/0.50  thf(d12_waybel_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.50                   ( ?[E:$i]:
% 0.21/0.50                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.21/0.50                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.21/0.50                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X16 : $i, X17 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X12)
% 0.21/0.50          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.21/0.50          | ~ (r2_waybel_0 @ X13 @ X12 @ X16)
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k2_waybel_0 @ X13 @ X12 @ (sk_E @ X17 @ X16 @ X12 @ X13)) @ X16)
% 0.21/0.50          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X12))
% 0.21/0.50          | ~ (l1_struct_0 @ X13)
% 0.21/0.50          | (v2_struct_0 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X1)
% 0.21/0.50          | ~ (l1_struct_0 @ X1)
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k2_waybel_0 @ X1 @ X0 @ 
% 0.21/0.50              (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1)) @ 
% 0.21/0.50             X2)
% 0.21/0.50          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.21/0.50          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B_1)
% 0.21/0.50          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.50             X0)
% 0.21/0.50          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['31', '34'])).
% 0.21/0.50  thf('36', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B_1)
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.50             X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.21/0.50  thf('39', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.50             X0))),
% 0.21/0.50      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (r2_hidden @ 
% 0.21/0.50          (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50           (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.50          X0)),
% 0.21/0.50      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.50  thf('43', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.50  thf('44', plain, ($false), inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
