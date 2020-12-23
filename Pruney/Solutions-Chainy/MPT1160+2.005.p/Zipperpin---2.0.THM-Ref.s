%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z9cXAyqjLc

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 103 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  584 (1143 expanded)
%              Number of equality atoms :   10 (  36 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t60_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_orders_2])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X14 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ X0 @ k1_xboole_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t57_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) )
                  <=> ( ( r2_orders_2 @ A @ B @ C )
                      & ( r2_hidden @ B @ D ) ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r2_hidden @ X17 @ ( k3_orders_2 @ X18 @ X19 @ X20 ) )
      | ( r2_hidden @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ X2 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k3_orders_2 @ X0 @ k1_xboole_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ X1 @ k1_xboole_0 @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ ( sk_C @ X2 @ ( k3_orders_2 @ X1 @ k1_xboole_0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_orders_2 @ X1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) ) @ k1_xboole_0 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) ) @ k1_xboole_0 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) ) @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('33',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('36',plain,
    ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','35'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X12: $i] :
      ( ( ( k1_struct_0 @ X12 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('38',plain,(
    ( k3_orders_2 @ sk_A @ ( k1_struct_0 @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('41',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z9cXAyqjLc
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:32:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 141 iterations in 0.098s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.53  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.20/0.53  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.53  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(d3_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf(t60_orders_2, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.53            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53              ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t60_orders_2])).
% 0.20/0.53  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t4_subset_1, axiom,
% 0.20/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.53  thf(dt_k3_orders_2, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.53         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @
% 0.20/0.53         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.53          | ~ (l1_orders_2 @ X14)
% 0.20/0.53          | ~ (v5_orders_2 @ X14)
% 0.20/0.53          | ~ (v4_orders_2 @ X14)
% 0.20/0.53          | ~ (v3_orders_2 @ X14)
% 0.20/0.53          | (v2_struct_0 @ X14)
% 0.20/0.53          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.20/0.53          | (m1_subset_1 @ (k3_orders_2 @ X14 @ X13 @ X15) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.53          | (v2_struct_0 @ X0)
% 0.20/0.53          | ~ (v3_orders_2 @ X0)
% 0.20/0.53          | ~ (v4_orders_2 @ X0)
% 0.20/0.53          | ~ (v5_orders_2 @ X0)
% 0.20/0.53          | ~ (l1_orders_2 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      ((~ (l1_orders_2 @ sk_A)
% 0.20/0.53        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.53        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.53        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ sk_A)
% 0.20/0.53        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.53  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.20/0.53  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf(t4_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X7 @ X8)
% 0.20/0.53          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.53          | (m1_subset_1 @ X7 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ X0)
% 0.20/0.53          | (m1_subset_1 @ 
% 0.20/0.53             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B)) @ 
% 0.20/0.53             (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.53  thf(t57_orders_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.20/0.53                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.20/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.53          | ~ (r2_hidden @ X17 @ (k3_orders_2 @ X18 @ X19 @ X20))
% 0.20/0.53          | (r2_hidden @ X17 @ X19)
% 0.20/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.20/0.53          | ~ (l1_orders_2 @ X18)
% 0.20/0.53          | ~ (v5_orders_2 @ X18)
% 0.20/0.53          | ~ (v4_orders_2 @ X18)
% 0.20/0.53          | ~ (v3_orders_2 @ X18)
% 0.20/0.53          | (v2_struct_0 @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X0)
% 0.20/0.53          | ~ (v3_orders_2 @ X0)
% 0.20/0.53          | ~ (v4_orders_2 @ X0)
% 0.20/0.53          | ~ (v5_orders_2 @ X0)
% 0.20/0.53          | ~ (l1_orders_2 @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.53          | (r2_hidden @ X2 @ k1_xboole_0)
% 0.20/0.53          | ~ (r2_hidden @ X2 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1))
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((r1_tarski @ (k3_orders_2 @ X1 @ k1_xboole_0 @ X0) @ X2)
% 0.20/0.53          | ~ (m1_subset_1 @ 
% 0.20/0.53               (sk_C @ X2 @ (k3_orders_2 @ X1 @ k1_xboole_0 @ X0)) @ 
% 0.20/0.53               (u1_struct_0 @ X1))
% 0.20/0.53          | (r2_hidden @ (sk_C @ X2 @ (k3_orders_2 @ X1 @ k1_xboole_0 @ X0)) @ 
% 0.20/0.53             k1_xboole_0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (l1_orders_2 @ X1)
% 0.20/0.53          | ~ (v5_orders_2 @ X1)
% 0.20/0.53          | ~ (v4_orders_2 @ X1)
% 0.20/0.53          | ~ (v3_orders_2 @ X1)
% 0.20/0.53          | (v2_struct_0 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B)) @ 
% 0.20/0.53             k1_xboole_0)
% 0.20/0.53          | (r1_tarski @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '20'])).
% 0.20/0.53  thf('22', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('23', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('24', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('26', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_A)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B)) @ 
% 0.20/0.53             k1_xboole_0)
% 0.20/0.53          | (r1_tarski @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '22', '23', '24', '25', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ 
% 0.20/0.53           (sk_C @ X0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B)) @ 
% 0.20/0.53           k1_xboole_0)
% 0.20/0.53          | (v2_struct_0 @ sk_A)
% 0.20/0.53          | (r1_tarski @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.53  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ X0)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B)) @ 
% 0.20/0.53             k1_xboole_0))),
% 0.20/0.53      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf(t7_ordinal1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ X0)
% 0.20/0.53          | ~ (r1_tarski @ k1_xboole_0 @ 
% 0.20/0.53               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.53  thf('33', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i]: (r1_tarski @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ X0)),
% 0.20/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf(t3_xboole_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.53  thf(d2_struct_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X12 : $i]:
% 0.20/0.53         (((k1_struct_0 @ X12) = (k1_xboole_0)) | ~ (l1_struct_0 @ X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (((k3_orders_2 @ sk_A @ (k1_struct_0 @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) != (k1_xboole_0))
% 0.20/0.53        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_l1_orders_2, axiom,
% 0.20/0.53    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_orders_2 @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.20/0.53  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) != (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['39', '42'])).
% 0.20/0.53  thf('44', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['36', '43'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
