%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q8fMTsongg

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 132 expanded)
%              Number of leaves         :   28 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  466 (1553 expanded)
%              Number of equality atoms :    5 (  53 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_orders_1 @ X15 @ ( k1_orders_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m2_orders_2 @ ( sk_C @ X15 @ X14 ) @ X14 @ X15 ) ) ),
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
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_orders_2,axiom,(
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
             => ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_orders_1 @ X16 @ ( k1_orders_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X16 @ ( u1_struct_0 @ X17 ) ) @ X18 )
      | ~ ( m2_orders_2 @ X18 @ X17 @ X16 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t79_orders_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m2_orders_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_orders_1 @ X8 @ ( k1_orders_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( X10
       != ( k4_orders_2 @ X9 @ X8 ) )
      | ( r2_hidden @ X11 @ X10 )
      | ~ ( m2_orders_2 @ X11 @ X9 @ X8 )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('26',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( m2_orders_2 @ X11 @ X9 @ X8 )
      | ( r2_hidden @ X11 @ ( k4_orders_2 @ X9 @ X8 ) )
      | ~ ( m1_orders_1 @ X8 @ ( k1_orders_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ ( k3_tarski @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('37',plain,(
    r1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('40',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['22','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q8fMTsongg
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 26 iterations in 0.017s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.21/0.46  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.46  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.21/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.46  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.21/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.46  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.46  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.46  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.46  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.46  thf(t87_orders_2, conjecture,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.46         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]:
% 0.21/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.46            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.46          ( ![B:$i]:
% 0.21/0.46            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(existence_m2_orders_2, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.46         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.21/0.46         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.46       ( ?[C:$i]: ( m2_orders_2 @ C @ A @ B ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X14 : $i, X15 : $i]:
% 0.21/0.46         (~ (l1_orders_2 @ X14)
% 0.21/0.46          | ~ (v5_orders_2 @ X14)
% 0.21/0.46          | ~ (v4_orders_2 @ X14)
% 0.21/0.46          | ~ (v3_orders_2 @ X14)
% 0.21/0.46          | (v2_struct_0 @ X14)
% 0.21/0.46          | ~ (m1_orders_1 @ X15 @ (k1_orders_1 @ (u1_struct_0 @ X14)))
% 0.21/0.46          | (m2_orders_2 @ (sk_C @ X15 @ X14) @ X14 @ X15))),
% 0.21/0.46      inference('cnf', [status(esa)], [existence_m2_orders_2])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (((m2_orders_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.21/0.46        | (v2_struct_0 @ sk_A)
% 0.21/0.46        | ~ (v3_orders_2 @ sk_A)
% 0.21/0.46        | ~ (v4_orders_2 @ sk_A)
% 0.21/0.46        | ~ (v5_orders_2 @ sk_A)
% 0.21/0.46        | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (((m2_orders_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.21/0.46        | (v2_struct_0 @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.21/0.46  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('9', plain, ((m2_orders_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.21/0.46      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t79_orders_2, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.46         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46           ( ![C:$i]:
% 0.21/0.46             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.46               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.46         (~ (m1_orders_1 @ X16 @ (k1_orders_1 @ (u1_struct_0 @ X17)))
% 0.21/0.46          | (r2_hidden @ (k1_funct_1 @ X16 @ (u1_struct_0 @ X17)) @ X18)
% 0.21/0.46          | ~ (m2_orders_2 @ X18 @ X17 @ X16)
% 0.21/0.46          | ~ (l1_orders_2 @ X17)
% 0.21/0.46          | ~ (v5_orders_2 @ X17)
% 0.21/0.46          | ~ (v4_orders_2 @ X17)
% 0.21/0.46          | ~ (v3_orders_2 @ X17)
% 0.21/0.46          | (v2_struct_0 @ X17))),
% 0.21/0.46      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((v2_struct_0 @ sk_A)
% 0.21/0.46          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.46          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.46          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.46          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.46          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.46          | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.46  thf('13', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('14', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('15', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('16', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((v2_struct_0 @ sk_A)
% 0.21/0.46          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.46          | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.21/0.46      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.21/0.46  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.21/0.46          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.21/0.46      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.46        (sk_C @ sk_B_1 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['9', '19'])).
% 0.21/0.46  thf(d1_xboole_0, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.46  thf('22', plain, (~ (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.46  thf('23', plain, ((m2_orders_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.21/0.46      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.46  thf('24', plain,
% 0.21/0.46      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(d17_orders_2, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.46         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46           ( ![C:$i]:
% 0.21/0.46             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.21/0.46               ( ![D:$i]:
% 0.21/0.46                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.46  thf('25', plain,
% 0.21/0.46      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.46         (~ (m1_orders_1 @ X8 @ (k1_orders_1 @ (u1_struct_0 @ X9)))
% 0.21/0.46          | ((X10) != (k4_orders_2 @ X9 @ X8))
% 0.21/0.46          | (r2_hidden @ X11 @ X10)
% 0.21/0.46          | ~ (m2_orders_2 @ X11 @ X9 @ X8)
% 0.21/0.46          | ~ (l1_orders_2 @ X9)
% 0.21/0.46          | ~ (v5_orders_2 @ X9)
% 0.21/0.46          | ~ (v4_orders_2 @ X9)
% 0.21/0.46          | ~ (v3_orders_2 @ X9)
% 0.21/0.46          | (v2_struct_0 @ X9))),
% 0.21/0.46      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.21/0.46  thf('26', plain,
% 0.21/0.46      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.21/0.46         ((v2_struct_0 @ X9)
% 0.21/0.46          | ~ (v3_orders_2 @ X9)
% 0.21/0.46          | ~ (v4_orders_2 @ X9)
% 0.21/0.46          | ~ (v5_orders_2 @ X9)
% 0.21/0.46          | ~ (l1_orders_2 @ X9)
% 0.21/0.46          | ~ (m2_orders_2 @ X11 @ X9 @ X8)
% 0.21/0.46          | (r2_hidden @ X11 @ (k4_orders_2 @ X9 @ X8))
% 0.21/0.46          | ~ (m1_orders_1 @ X8 @ (k1_orders_1 @ (u1_struct_0 @ X9))))),
% 0.21/0.46      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.46  thf('27', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.46          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.46          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.46          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.46          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.46          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.46          | (v2_struct_0 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['24', '26'])).
% 0.21/0.46  thf('28', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('29', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('30', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('31', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('32', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.46          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.46          | (v2_struct_0 @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.21/0.46  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('34', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.46          | (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.21/0.46      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.46  thf('35', plain,
% 0.21/0.46      ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.21/0.46      inference('sup-', [status(thm)], ['23', '34'])).
% 0.21/0.46  thf(l49_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.46  thf('36', plain,
% 0.21/0.46      (![X6 : $i, X7 : $i]:
% 0.21/0.46         ((r1_tarski @ X6 @ (k3_tarski @ X7)) | ~ (r2_hidden @ X6 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.21/0.46  thf('37', plain,
% 0.21/0.46      ((r1_tarski @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.21/0.46        (k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.46  thf('38', plain,
% 0.21/0.46      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('39', plain, ((r1_tarski @ (sk_C @ sk_B_1 @ sk_A) @ k1_xboole_0)),
% 0.21/0.46      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.46  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.46  thf('40', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.21/0.46      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.46  thf(t69_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.46       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.46  thf('41', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i]:
% 0.21/0.46         (~ (r1_xboole_0 @ X4 @ X5)
% 0.21/0.46          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.46          | (v1_xboole_0 @ X4))),
% 0.21/0.46      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.46  thf('42', plain,
% 0.21/0.46      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.46  thf('43', plain, ((v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['39', '42'])).
% 0.21/0.46  thf('44', plain, ($false), inference('demod', [status(thm)], ['22', '43'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
