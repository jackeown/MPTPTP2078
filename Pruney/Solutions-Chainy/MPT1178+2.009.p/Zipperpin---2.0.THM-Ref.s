%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GAZlaRmGPW

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:21 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 219 expanded)
%              Number of leaves         :   27 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  490 (2752 expanded)
%              Number of equality atoms :    9 ( 102 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t87_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) )
           != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) )
             != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_orders_2])).

thf('0',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ? [C: $i] :
          ( m2_orders_2 @ C @ A @ B ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_orders_1 @ X19 @ ( k1_orders_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m2_orders_2 @ ( sk_C @ X19 @ X18 ) @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[existence_m2_orders_2])).

thf('2',plain,
    ( ( m2_orders_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m2_orders_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m2_orders_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m2_orders_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('11',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d17_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( C
                = ( k4_orders_2 @ A @ B ) )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ C )
                <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_orders_1 @ X12 @ ( k1_orders_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( X14
       != ( k4_orders_2 @ X13 @ X12 ) )
      | ( r2_hidden @ X15 @ X14 )
      | ~ ( m2_orders_2 @ X15 @ X13 @ X12 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('13',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( m2_orders_2 @ X15 @ X13 @ X12 )
      | ( r2_hidden @ X15 @ ( k4_orders_2 @ X13 @ X12 ) )
      | ~ ( m1_orders_1 @ X12 @ ( k1_orders_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ ( k3_tarski @ X11 ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('24',plain,(
    r1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_C @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['9','30'])).

thf('32',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['9','30'])).

thf('33',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t82_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ~ ( r1_xboole_0 @ C @ D ) ) ) ) ) )).

thf('34',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_orders_1 @ X22 @ ( k1_orders_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m2_orders_2 @ X24 @ X23 @ X22 )
      | ~ ( r1_xboole_0 @ X25 @ X24 )
      | ~ ( m2_orders_2 @ X25 @ X23 @ X22 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t82_orders_2])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('42',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference('sup-',[status(thm)],['31','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GAZlaRmGPW
% 0.16/0.37  % Computer   : n003.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 19:49:57 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.45  % Solved by: fo/fo7.sh
% 0.23/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.45  % done 45 iterations in 0.013s
% 0.23/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.45  % SZS output start Refutation
% 0.23/0.45  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.23/0.45  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.23/0.45  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.23/0.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.45  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.23/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.45  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.23/0.45  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.23/0.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.45  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.45  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.23/0.45  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.23/0.45  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.23/0.45  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.45  thf(t87_orders_2, conjecture,
% 0.23/0.45    (![A:$i]:
% 0.23/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.45         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.45       ( ![B:$i]:
% 0.23/0.45         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.45           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.23/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.45    (~( ![A:$i]:
% 0.23/0.45        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.45            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.45          ( ![B:$i]:
% 0.23/0.45            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.45              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.23/0.45    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.23/0.45  thf('0', plain,
% 0.23/0.45      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf(existence_m2_orders_2, axiom,
% 0.23/0.45    (![A:$i,B:$i]:
% 0.23/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.45         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.23/0.45         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.45       ( ?[C:$i]: ( m2_orders_2 @ C @ A @ B ) ) ))).
% 0.23/0.45  thf('1', plain,
% 0.23/0.45      (![X18 : $i, X19 : $i]:
% 0.23/0.45         (~ (l1_orders_2 @ X18)
% 0.23/0.45          | ~ (v5_orders_2 @ X18)
% 0.23/0.45          | ~ (v4_orders_2 @ X18)
% 0.23/0.45          | ~ (v3_orders_2 @ X18)
% 0.23/0.45          | (v2_struct_0 @ X18)
% 0.23/0.45          | ~ (m1_orders_1 @ X19 @ (k1_orders_1 @ (u1_struct_0 @ X18)))
% 0.23/0.45          | (m2_orders_2 @ (sk_C @ X19 @ X18) @ X18 @ X19))),
% 0.23/0.45      inference('cnf', [status(esa)], [existence_m2_orders_2])).
% 0.23/0.45  thf('2', plain,
% 0.23/0.45      (((m2_orders_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.23/0.45        | (v2_struct_0 @ sk_A)
% 0.23/0.45        | ~ (v3_orders_2 @ sk_A)
% 0.23/0.45        | ~ (v4_orders_2 @ sk_A)
% 0.23/0.45        | ~ (v5_orders_2 @ sk_A)
% 0.23/0.45        | ~ (l1_orders_2 @ sk_A))),
% 0.23/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.45  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('7', plain,
% 0.23/0.45      (((m2_orders_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.23/0.45        | (v2_struct_0 @ sk_A))),
% 0.23/0.45      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.23/0.45  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('9', plain, ((m2_orders_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.23/0.45      inference('clc', [status(thm)], ['7', '8'])).
% 0.23/0.45  thf('10', plain, ((m2_orders_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.23/0.45      inference('clc', [status(thm)], ['7', '8'])).
% 0.23/0.45  thf('11', plain,
% 0.23/0.45      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf(d17_orders_2, axiom,
% 0.23/0.45    (![A:$i]:
% 0.23/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.45         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.45       ( ![B:$i]:
% 0.23/0.45         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.45           ( ![C:$i]:
% 0.23/0.45             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.23/0.45               ( ![D:$i]:
% 0.23/0.45                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.23/0.45  thf('12', plain,
% 0.23/0.45      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.45         (~ (m1_orders_1 @ X12 @ (k1_orders_1 @ (u1_struct_0 @ X13)))
% 0.23/0.45          | ((X14) != (k4_orders_2 @ X13 @ X12))
% 0.23/0.45          | (r2_hidden @ X15 @ X14)
% 0.23/0.45          | ~ (m2_orders_2 @ X15 @ X13 @ X12)
% 0.23/0.45          | ~ (l1_orders_2 @ X13)
% 0.23/0.45          | ~ (v5_orders_2 @ X13)
% 0.23/0.45          | ~ (v4_orders_2 @ X13)
% 0.23/0.45          | ~ (v3_orders_2 @ X13)
% 0.23/0.45          | (v2_struct_0 @ X13))),
% 0.23/0.45      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.23/0.45  thf('13', plain,
% 0.23/0.45      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.23/0.45         ((v2_struct_0 @ X13)
% 0.23/0.45          | ~ (v3_orders_2 @ X13)
% 0.23/0.45          | ~ (v4_orders_2 @ X13)
% 0.23/0.45          | ~ (v5_orders_2 @ X13)
% 0.23/0.45          | ~ (l1_orders_2 @ X13)
% 0.23/0.45          | ~ (m2_orders_2 @ X15 @ X13 @ X12)
% 0.23/0.45          | (r2_hidden @ X15 @ (k4_orders_2 @ X13 @ X12))
% 0.23/0.45          | ~ (m1_orders_1 @ X12 @ (k1_orders_1 @ (u1_struct_0 @ X13))))),
% 0.23/0.45      inference('simplify', [status(thm)], ['12'])).
% 0.23/0.45  thf('14', plain,
% 0.23/0.45      (![X0 : $i]:
% 0.23/0.45         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.23/0.45          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.23/0.45          | ~ (l1_orders_2 @ sk_A)
% 0.23/0.45          | ~ (v5_orders_2 @ sk_A)
% 0.23/0.45          | ~ (v4_orders_2 @ sk_A)
% 0.23/0.45          | ~ (v3_orders_2 @ sk_A)
% 0.23/0.45          | (v2_struct_0 @ sk_A))),
% 0.23/0.45      inference('sup-', [status(thm)], ['11', '13'])).
% 0.23/0.45  thf('15', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('16', plain, ((v5_orders_2 @ sk_A)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('17', plain, ((v4_orders_2 @ sk_A)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('18', plain, ((v3_orders_2 @ sk_A)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('19', plain,
% 0.23/0.45      (![X0 : $i]:
% 0.23/0.45         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.23/0.45          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.23/0.45          | (v2_struct_0 @ sk_A))),
% 0.23/0.45      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.23/0.45  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('21', plain,
% 0.23/0.45      (![X0 : $i]:
% 0.23/0.45         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.23/0.45          | (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.23/0.45      inference('clc', [status(thm)], ['19', '20'])).
% 0.23/0.45  thf('22', plain,
% 0.23/0.45      ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.23/0.45      inference('sup-', [status(thm)], ['10', '21'])).
% 0.23/0.45  thf(l49_zfmisc_1, axiom,
% 0.23/0.45    (![A:$i,B:$i]:
% 0.23/0.45     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.23/0.45  thf('23', plain,
% 0.23/0.45      (![X10 : $i, X11 : $i]:
% 0.23/0.45         ((r1_tarski @ X10 @ (k3_tarski @ X11)) | ~ (r2_hidden @ X10 @ X11))),
% 0.23/0.45      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.23/0.45  thf('24', plain,
% 0.23/0.45      ((r1_tarski @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.23/0.45        (k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.23/0.45      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.45  thf('25', plain,
% 0.23/0.45      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('26', plain, ((r1_tarski @ (sk_C @ sk_B_1 @ sk_A) @ k1_xboole_0)),
% 0.23/0.45      inference('demod', [status(thm)], ['24', '25'])).
% 0.23/0.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.23/0.45  thf('27', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.23/0.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.23/0.45  thf(d10_xboole_0, axiom,
% 0.23/0.45    (![A:$i,B:$i]:
% 0.23/0.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.45  thf('28', plain,
% 0.23/0.45      (![X5 : $i, X7 : $i]:
% 0.23/0.45         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.23/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.45  thf('29', plain,
% 0.23/0.45      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.23/0.45      inference('sup-', [status(thm)], ['27', '28'])).
% 0.23/0.45  thf('30', plain, (((sk_C @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.23/0.45      inference('sup-', [status(thm)], ['26', '29'])).
% 0.23/0.45  thf('31', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.23/0.45      inference('demod', [status(thm)], ['9', '30'])).
% 0.23/0.45  thf('32', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.23/0.45      inference('demod', [status(thm)], ['9', '30'])).
% 0.23/0.45  thf('33', plain,
% 0.23/0.45      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf(t82_orders_2, axiom,
% 0.23/0.45    (![A:$i]:
% 0.23/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.45         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.45       ( ![B:$i]:
% 0.23/0.45         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.45           ( ![C:$i]:
% 0.23/0.45             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.23/0.45               ( ![D:$i]:
% 0.23/0.45                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.23/0.45  thf('34', plain,
% 0.23/0.45      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.23/0.45         (~ (m1_orders_1 @ X22 @ (k1_orders_1 @ (u1_struct_0 @ X23)))
% 0.23/0.45          | ~ (m2_orders_2 @ X24 @ X23 @ X22)
% 0.23/0.45          | ~ (r1_xboole_0 @ X25 @ X24)
% 0.23/0.45          | ~ (m2_orders_2 @ X25 @ X23 @ X22)
% 0.23/0.45          | ~ (l1_orders_2 @ X23)
% 0.23/0.45          | ~ (v5_orders_2 @ X23)
% 0.23/0.45          | ~ (v4_orders_2 @ X23)
% 0.23/0.45          | ~ (v3_orders_2 @ X23)
% 0.23/0.45          | (v2_struct_0 @ X23))),
% 0.23/0.45      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.23/0.45  thf('35', plain,
% 0.23/0.45      (![X0 : $i, X1 : $i]:
% 0.23/0.45         ((v2_struct_0 @ sk_A)
% 0.23/0.45          | ~ (v3_orders_2 @ sk_A)
% 0.23/0.45          | ~ (v4_orders_2 @ sk_A)
% 0.23/0.45          | ~ (v5_orders_2 @ sk_A)
% 0.23/0.45          | ~ (l1_orders_2 @ sk_A)
% 0.23/0.45          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.23/0.45          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.23/0.45          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.23/0.45      inference('sup-', [status(thm)], ['33', '34'])).
% 0.23/0.45  thf('36', plain, ((v3_orders_2 @ sk_A)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('37', plain, ((v4_orders_2 @ sk_A)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('38', plain, ((v5_orders_2 @ sk_A)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('40', plain,
% 0.23/0.45      (![X0 : $i, X1 : $i]:
% 0.23/0.45         ((v2_struct_0 @ sk_A)
% 0.23/0.45          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.23/0.45          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.23/0.45          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.23/0.45      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.23/0.45  thf('41', plain,
% 0.23/0.45      (![X0 : $i]:
% 0.23/0.45         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.23/0.45          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.23/0.45          | (v2_struct_0 @ sk_A))),
% 0.23/0.45      inference('sup-', [status(thm)], ['32', '40'])).
% 0.23/0.45  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.23/0.45  thf('42', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.23/0.45      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.23/0.45  thf(symmetry_r1_xboole_0, axiom,
% 0.23/0.45    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.23/0.45  thf('43', plain,
% 0.23/0.45      (![X3 : $i, X4 : $i]:
% 0.23/0.45         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.23/0.45      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.23/0.45  thf('44', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.23/0.45      inference('sup-', [status(thm)], ['42', '43'])).
% 0.23/0.45  thf('45', plain,
% 0.23/0.45      (![X0 : $i]:
% 0.23/0.45         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 0.23/0.45      inference('demod', [status(thm)], ['41', '44'])).
% 0.23/0.45  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('47', plain, (![X0 : $i]: ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)),
% 0.23/0.45      inference('clc', [status(thm)], ['45', '46'])).
% 0.23/0.45  thf('48', plain, ($false), inference('sup-', [status(thm)], ['31', '47'])).
% 0.23/0.45  
% 0.23/0.45  % SZS output end Refutation
% 0.23/0.45  
% 0.23/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
