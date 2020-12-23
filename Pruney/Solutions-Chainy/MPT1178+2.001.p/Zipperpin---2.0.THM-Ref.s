%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XQJd15euUS

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:20 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 222 expanded)
%              Number of leaves         :   29 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :  529 (2836 expanded)
%              Number of equality atoms :   13 ( 105 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t78_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) ) @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_orders_1 @ X32 @ ( k1_orders_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ X32 @ ( u1_struct_0 @ X33 ) ) ) @ X33 @ X32 )
      | ~ ( l1_orders_2 @ X33 )
      | ~ ( v5_orders_2 @ X33 )
      | ~ ( v4_orders_2 @ X33 )
      | ~ ( v3_orders_2 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t78_orders_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ sk_B ) ),
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
    ( ( v2_struct_0 @ sk_A )
    | ( m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['7','8'])).

thf('11',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_orders_1 @ X24 @ ( k1_orders_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( X26
       != ( k4_orders_2 @ X25 @ X24 ) )
      | ( r2_hidden @ X27 @ X26 )
      | ~ ( m2_orders_2 @ X27 @ X25 @ X24 )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('13',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( m2_orders_2 @ X27 @ X25 @ X24 )
      | ( r2_hidden @ X27 @ ( k4_orders_2 @ X25 @ X24 ) )
      | ~ ( m1_orders_1 @ X24 @ ( k1_orders_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
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
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ ( k4_orders_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('24',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X21 @ X19 )
      | ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_orders_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('26',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_orders_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('30',plain,
    ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['9','30'])).

thf('32',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['9','30'])).

thf('33',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_orders_1 @ X34 @ ( k1_orders_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m2_orders_2 @ X36 @ X35 @ X34 )
      | ~ ( r1_xboole_0 @ X37 @ X36 )
      | ~ ( m2_orders_2 @ X37 @ X35 @ X34 )
      | ~ ( l1_orders_2 @ X35 )
      | ~ ( v5_orders_2 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v3_orders_2 @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t82_orders_2])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
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
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('42',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('43',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ X13 )
      | ( ( k4_xboole_0 @ X11 @ X13 )
       != X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference('sup-',[status(thm)],['31','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XQJd15euUS
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:41:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 232 iterations in 0.061s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.34/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.34/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.34/0.52  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.34/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.34/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.34/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.52  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.34/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.34/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.34/0.52  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.34/0.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.34/0.52  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.34/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.52  thf(t87_orders_2, conjecture,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.34/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.34/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.52    (~( ![A:$i]:
% 0.34/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.34/0.52            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.34/0.52          ( ![B:$i]:
% 0.34/0.52            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.34/0.52    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.34/0.52  thf('0', plain,
% 0.34/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(t78_orders_2, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.34/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52           ( m2_orders_2 @
% 0.34/0.52             ( k1_tarski @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) ) @ A @ B ) ) ) ))).
% 0.34/0.52  thf('1', plain,
% 0.34/0.52      (![X32 : $i, X33 : $i]:
% 0.34/0.52         (~ (m1_orders_1 @ X32 @ (k1_orders_1 @ (u1_struct_0 @ X33)))
% 0.34/0.52          | (m2_orders_2 @ 
% 0.34/0.52             (k1_tarski @ (k1_funct_1 @ X32 @ (u1_struct_0 @ X33))) @ X33 @ X32)
% 0.34/0.52          | ~ (l1_orders_2 @ X33)
% 0.34/0.52          | ~ (v5_orders_2 @ X33)
% 0.34/0.52          | ~ (v4_orders_2 @ X33)
% 0.34/0.52          | ~ (v3_orders_2 @ X33)
% 0.34/0.52          | (v2_struct_0 @ X33))),
% 0.34/0.52      inference('cnf', [status(esa)], [t78_orders_2])).
% 0.34/0.52  thf('2', plain,
% 0.34/0.52      (((v2_struct_0 @ sk_A)
% 0.34/0.52        | ~ (v3_orders_2 @ sk_A)
% 0.34/0.52        | ~ (v4_orders_2 @ sk_A)
% 0.34/0.52        | ~ (v5_orders_2 @ sk_A)
% 0.34/0.52        | ~ (l1_orders_2 @ sk_A)
% 0.34/0.52        | (m2_orders_2 @ 
% 0.34/0.52           (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ sk_A @ 
% 0.34/0.52           sk_B))),
% 0.34/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.34/0.52  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('7', plain,
% 0.34/0.52      (((v2_struct_0 @ sk_A)
% 0.34/0.52        | (m2_orders_2 @ 
% 0.34/0.52           (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ sk_A @ 
% 0.34/0.52           sk_B))),
% 0.34/0.52      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.34/0.52  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('9', plain,
% 0.34/0.52      ((m2_orders_2 @ 
% 0.34/0.52        (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ sk_A @ sk_B)),
% 0.34/0.52      inference('clc', [status(thm)], ['7', '8'])).
% 0.34/0.52  thf('10', plain,
% 0.34/0.52      ((m2_orders_2 @ 
% 0.34/0.52        (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ sk_A @ sk_B)),
% 0.34/0.52      inference('clc', [status(thm)], ['7', '8'])).
% 0.34/0.52  thf('11', plain,
% 0.34/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(d17_orders_2, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.34/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52           ( ![C:$i]:
% 0.34/0.52             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.34/0.52               ( ![D:$i]:
% 0.34/0.52                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.34/0.52  thf('12', plain,
% 0.34/0.52      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.34/0.52         (~ (m1_orders_1 @ X24 @ (k1_orders_1 @ (u1_struct_0 @ X25)))
% 0.34/0.52          | ((X26) != (k4_orders_2 @ X25 @ X24))
% 0.34/0.52          | (r2_hidden @ X27 @ X26)
% 0.34/0.52          | ~ (m2_orders_2 @ X27 @ X25 @ X24)
% 0.34/0.52          | ~ (l1_orders_2 @ X25)
% 0.34/0.52          | ~ (v5_orders_2 @ X25)
% 0.34/0.52          | ~ (v4_orders_2 @ X25)
% 0.34/0.52          | ~ (v3_orders_2 @ X25)
% 0.34/0.52          | (v2_struct_0 @ X25))),
% 0.34/0.52      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.34/0.52  thf('13', plain,
% 0.34/0.52      (![X24 : $i, X25 : $i, X27 : $i]:
% 0.34/0.52         ((v2_struct_0 @ X25)
% 0.34/0.52          | ~ (v3_orders_2 @ X25)
% 0.34/0.52          | ~ (v4_orders_2 @ X25)
% 0.34/0.52          | ~ (v5_orders_2 @ X25)
% 0.34/0.52          | ~ (l1_orders_2 @ X25)
% 0.34/0.52          | ~ (m2_orders_2 @ X27 @ X25 @ X24)
% 0.34/0.52          | (r2_hidden @ X27 @ (k4_orders_2 @ X25 @ X24))
% 0.34/0.52          | ~ (m1_orders_1 @ X24 @ (k1_orders_1 @ (u1_struct_0 @ X25))))),
% 0.34/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.34/0.52  thf('14', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B))
% 0.34/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.34/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.34/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.34/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.34/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.34/0.52          | (v2_struct_0 @ sk_A))),
% 0.34/0.52      inference('sup-', [status(thm)], ['11', '13'])).
% 0.34/0.52  thf('15', plain, ((l1_orders_2 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('16', plain, ((v5_orders_2 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('17', plain, ((v4_orders_2 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('18', plain, ((v3_orders_2 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('19', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B))
% 0.34/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.34/0.52          | (v2_struct_0 @ sk_A))),
% 0.34/0.52      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.34/0.52  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('21', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.34/0.52          | (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B)))),
% 0.34/0.52      inference('clc', [status(thm)], ['19', '20'])).
% 0.34/0.52  thf('22', plain,
% 0.34/0.52      ((r2_hidden @ (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.34/0.52        (k4_orders_2 @ sk_A @ sk_B))),
% 0.34/0.52      inference('sup-', [status(thm)], ['10', '21'])).
% 0.34/0.52  thf('23', plain,
% 0.34/0.52      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(t56_setfam_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.34/0.52       ( r1_tarski @ C @ B ) ))).
% 0.34/0.52  thf('24', plain,
% 0.34/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.34/0.52         (~ (r1_tarski @ (k3_tarski @ X19) @ X20)
% 0.34/0.52          | ~ (r2_hidden @ X21 @ X19)
% 0.34/0.52          | (r1_tarski @ X21 @ X20))),
% 0.34/0.52      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.34/0.52  thf('25', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.34/0.52          | (r1_tarski @ X1 @ X0)
% 0.34/0.52          | ~ (r2_hidden @ X1 @ (k4_orders_2 @ sk_A @ sk_B)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.34/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.34/0.52  thf('26', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.34/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.34/0.52  thf('27', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r1_tarski @ X1 @ X0)
% 0.34/0.52          | ~ (r2_hidden @ X1 @ (k4_orders_2 @ sk_A @ sk_B)))),
% 0.34/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.34/0.52  thf('28', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (r1_tarski @ 
% 0.34/0.52          (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ X0)),
% 0.34/0.52      inference('sup-', [status(thm)], ['22', '27'])).
% 0.34/0.52  thf(t3_xboole_1, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.34/0.52  thf('29', plain,
% 0.34/0.52      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.34/0.52      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.34/0.52  thf('30', plain,
% 0.34/0.52      (((k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.34/0.52         = (k1_xboole_0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.34/0.52  thf('31', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B)),
% 0.34/0.52      inference('demod', [status(thm)], ['9', '30'])).
% 0.34/0.52  thf('32', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B)),
% 0.34/0.52      inference('demod', [status(thm)], ['9', '30'])).
% 0.34/0.52  thf('33', plain,
% 0.34/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(t82_orders_2, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.34/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52           ( ![C:$i]:
% 0.34/0.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.34/0.52               ( ![D:$i]:
% 0.34/0.52                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.34/0.52  thf('34', plain,
% 0.34/0.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.34/0.52         (~ (m1_orders_1 @ X34 @ (k1_orders_1 @ (u1_struct_0 @ X35)))
% 0.34/0.52          | ~ (m2_orders_2 @ X36 @ X35 @ X34)
% 0.34/0.52          | ~ (r1_xboole_0 @ X37 @ X36)
% 0.34/0.52          | ~ (m2_orders_2 @ X37 @ X35 @ X34)
% 0.34/0.52          | ~ (l1_orders_2 @ X35)
% 0.34/0.52          | ~ (v5_orders_2 @ X35)
% 0.34/0.52          | ~ (v4_orders_2 @ X35)
% 0.34/0.52          | ~ (v3_orders_2 @ X35)
% 0.34/0.52          | (v2_struct_0 @ X35))),
% 0.34/0.52      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.34/0.52  thf('35', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((v2_struct_0 @ sk_A)
% 0.34/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.34/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.34/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.34/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.34/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.34/0.52          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.34/0.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.34/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.34/0.52  thf('36', plain, ((v3_orders_2 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('37', plain, ((v4_orders_2 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('38', plain, ((v5_orders_2 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('40', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((v2_struct_0 @ sk_A)
% 0.34/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.34/0.52          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.34/0.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.34/0.52      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.34/0.52  thf('41', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.34/0.52          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.34/0.52          | (v2_struct_0 @ sk_A))),
% 0.34/0.52      inference('sup-', [status(thm)], ['32', '40'])).
% 0.34/0.52  thf(t4_boole, axiom,
% 0.34/0.52    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.34/0.52  thf('42', plain,
% 0.34/0.52      (![X7 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.34/0.52      inference('cnf', [status(esa)], [t4_boole])).
% 0.34/0.52  thf(t83_xboole_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.34/0.52  thf('43', plain,
% 0.34/0.52      (![X11 : $i, X13 : $i]:
% 0.34/0.52         ((r1_xboole_0 @ X11 @ X13) | ((k4_xboole_0 @ X11 @ X13) != (X11)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.34/0.52  thf('44', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.34/0.52  thf('45', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.34/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.34/0.52  thf('46', plain,
% 0.34/0.52      (![X0 : $i]: (~ (m2_orders_2 @ X0 @ sk_A @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.34/0.52      inference('demod', [status(thm)], ['41', '45'])).
% 0.34/0.52  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('48', plain, (![X0 : $i]: ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)),
% 0.34/0.52      inference('clc', [status(thm)], ['46', '47'])).
% 0.34/0.52  thf('49', plain, ($false), inference('sup-', [status(thm)], ['31', '48'])).
% 0.34/0.52  
% 0.34/0.52  % SZS output end Refutation
% 0.34/0.52  
% 0.36/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
