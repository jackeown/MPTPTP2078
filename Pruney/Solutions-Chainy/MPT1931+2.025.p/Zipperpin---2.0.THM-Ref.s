%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x5Rxh1GDQe

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 104 expanded)
%              Number of leaves         :   33 (  47 expanded)
%              Depth                    :   17
%              Number of atoms          :  497 ( 949 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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

thf('1',plain,(
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

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( r1_waybel_0 @ X19 @ X18 @ ( k6_subset_1 @ ( u1_struct_0 @ X19 ) @ X20 ) )
      | ( r2_waybel_0 @ X19 @ X18 @ X20 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( r1_waybel_0 @ X19 @ X18 @ ( k4_xboole_0 @ ( u1_struct_0 @ X19 ) @ X20 ) )
      | ( r2_waybel_0 @ X19 @ X18 @ X20 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','7'])).

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

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('19',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X7 ) @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['16','17','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('29',plain,(
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

thf('30',plain,(
    ! [X12: $i,X13: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( r2_waybel_0 @ X13 @ X12 @ X16 )
      | ( r2_hidden @ ( k2_waybel_0 @ X13 @ X12 @ ( sk_E @ X17 @ X16 @ X12 @ X13 ) ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('41',plain,(
    $false ),
    inference('sup-',[status(thm)],['39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x5Rxh1GDQe
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 48 iterations in 0.029s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.20/0.48  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.48  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.20/0.48  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(t3_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.48  thf('0', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.48  thf(t29_yellow_6, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.48             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.48           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.48                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.48              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.20/0.48  thf('1', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t10_waybel_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.20/0.48               ( ~( r1_waybel_0 @
% 0.20/0.48                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X18)
% 0.20/0.48          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.20/0.48          | (r1_waybel_0 @ X19 @ X18 @ 
% 0.20/0.48             (k6_subset_1 @ (u1_struct_0 @ X19) @ X20))
% 0.20/0.48          | (r2_waybel_0 @ X19 @ X18 @ X20)
% 0.20/0.48          | ~ (l1_struct_0 @ X19)
% 0.20/0.48          | (v2_struct_0 @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.20/0.48  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         ((k6_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X18)
% 0.20/0.48          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.20/0.48          | (r1_waybel_0 @ X19 @ X18 @ 
% 0.20/0.48             (k4_xboole_0 @ (u1_struct_0 @ X19) @ X20))
% 0.20/0.48          | (r2_waybel_0 @ X19 @ X18 @ X20)
% 0.20/0.48          | ~ (l1_struct_0 @ X19)
% 0.20/0.48          | (v2_struct_0 @ X19))),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.48          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.48             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.48          | (v2_struct_0 @ sk_B_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.48  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.48             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.48          | (v2_struct_0 @ sk_B_1))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (((r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v2_struct_0 @ sk_B_1)
% 0.20/0.48        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup+', [status(thm)], ['0', '7'])).
% 0.20/0.48  thf('9', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.20/0.48        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain, ((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)),
% 0.20/0.48      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf(t8_waybel_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.48           ( ![C:$i,D:$i]:
% 0.20/0.48             ( ( r1_tarski @ C @ D ) =>
% 0.20/0.48               ( ( ( r1_waybel_0 @ A @ B @ C ) => ( r1_waybel_0 @ A @ B @ D ) ) & 
% 0.20/0.48                 ( ( r2_waybel_0 @ A @ B @ C ) => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X22)
% 0.20/0.48          | ~ (l1_waybel_0 @ X22 @ X23)
% 0.20/0.48          | ~ (r2_waybel_0 @ X23 @ X22 @ X24)
% 0.20/0.48          | (r2_waybel_0 @ X23 @ X22 @ X25)
% 0.20/0.48          | ~ (r1_tarski @ X24 @ X25)
% 0.20/0.48          | ~ (l1_struct_0 @ X23)
% 0.20/0.48          | (v2_struct_0 @ X23))),
% 0.20/0.48      inference('cnf', [status(esa)], [t8_waybel_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.48          | ~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.20/0.48          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.48          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_B_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d3_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]:
% 0.20/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.48  thf('19', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.20/0.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.48  thf(l24_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ (k1_tarski @ X7) @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.20/0.48  thf('21', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.48  thf('23', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_B_1))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '17', '22', '23'])).
% 0.20/0.48  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0))),
% 0.20/0.48      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('28', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 0.20/0.48      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf(existence_m1_subset_1, axiom,
% 0.20/0.48    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.20/0.48  thf('29', plain, (![X9 : $i]: (m1_subset_1 @ (sk_B @ X9) @ X9)),
% 0.20/0.48      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.20/0.48  thf(d12_waybel_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.20/0.48               ( ![D:$i]:
% 0.20/0.48                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.48                   ( ?[E:$i]:
% 0.20/0.48                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.20/0.48                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.20/0.48                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i, X16 : $i, X17 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X12)
% 0.20/0.48          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.20/0.48          | ~ (r2_waybel_0 @ X13 @ X12 @ X16)
% 0.20/0.48          | (r2_hidden @ 
% 0.20/0.48             (k2_waybel_0 @ X13 @ X12 @ (sk_E @ X17 @ X16 @ X12 @ X13)) @ X16)
% 0.20/0.48          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X12))
% 0.20/0.48          | ~ (l1_struct_0 @ X13)
% 0.20/0.48          | (v2_struct_0 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X1)
% 0.20/0.48          | ~ (l1_struct_0 @ X1)
% 0.20/0.48          | (r2_hidden @ 
% 0.20/0.48             (k2_waybel_0 @ X1 @ X0 @ 
% 0.20/0.48              (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1)) @ 
% 0.20/0.48             X2)
% 0.20/0.48          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.20/0.48          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_B_1)
% 0.20/0.48          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.20/0.48          | (r2_hidden @ 
% 0.20/0.48             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.48              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.20/0.48             X0)
% 0.20/0.48          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '31'])).
% 0.20/0.48  thf('33', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_B_1)
% 0.20/0.48          | (r2_hidden @ 
% 0.20/0.48             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.48              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.20/0.48             X0)
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.48  thf('36', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | (r2_hidden @ 
% 0.20/0.48             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.48              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.20/0.48             X0))),
% 0.20/0.48      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (r2_hidden @ 
% 0.20/0.48          (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.48           (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.20/0.48          X0)),
% 0.20/0.48      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('40', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('41', plain, ($false), inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
