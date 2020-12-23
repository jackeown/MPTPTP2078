%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4itZKWSAMU

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:29 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   62 (  87 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  393 ( 904 expanded)
%              Number of equality atoms :    7 (  31 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_orders_1 @ X33 @ ( k1_orders_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ X33 @ ( u1_struct_0 @ X34 ) ) ) @ X34 @ X33 )
      | ~ ( l1_orders_2 @ X34 )
      | ~ ( v5_orders_2 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ~ ( v3_orders_2 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
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

thf('11',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_orders_1 @ X27 @ ( k1_orders_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( X29
       != ( k4_orders_2 @ X28 @ X27 ) )
      | ( r2_hidden @ X30 @ X29 )
      | ~ ( m2_orders_2 @ X30 @ X28 @ X27 )
      | ~ ( l1_orders_2 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('12',plain,(
    ! [X27: $i,X28: $i,X30: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( l1_orders_2 @ X28 )
      | ~ ( m2_orders_2 @ X30 @ X28 @ X27 )
      | ( r2_hidden @ X30 @ ( k4_orders_2 @ X28 @ X27 ) )
      | ~ ( m1_orders_1 @ X27 @ ( k1_orders_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ ( k4_orders_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('22',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X19 ) @ X21 )
      | ~ ( r2_hidden @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('23',plain,(
    r1_tarski @ ( k1_tarski @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) @ ( k4_orders_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('24',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X23 ) @ ( k3_tarski @ X24 ) )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('25',plain,(
    r1_tarski @ ( k3_tarski @ ( k1_tarski @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ) @ ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('26',plain,(
    ! [X22: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('27',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r1_tarski @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ ( k1_tarski @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('30',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('32',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4itZKWSAMU
% 0.13/0.38  % Computer   : n013.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 17:50:10 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.24/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.53  % Solved by: fo/fo7.sh
% 0.24/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.53  % done 76 iterations in 0.046s
% 0.24/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.53  % SZS output start Refutation
% 0.24/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.24/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.53  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.24/0.53  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.24/0.53  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.24/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.24/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.53  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.24/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.24/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.53  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.24/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.53  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.24/0.53  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.24/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.53  thf(t87_orders_2, conjecture,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.24/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.24/0.53       ( ![B:$i]:
% 0.24/0.53         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.24/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.53    (~( ![A:$i]:
% 0.24/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.24/0.53            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.24/0.53          ( ![B:$i]:
% 0.24/0.53            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.24/0.53    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.24/0.53  thf('0', plain,
% 0.24/0.53      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(t78_orders_2, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.24/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.24/0.53       ( ![B:$i]:
% 0.24/0.53         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53           ( m2_orders_2 @
% 0.24/0.53             ( k1_tarski @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) ) @ A @ B ) ) ) ))).
% 0.24/0.53  thf('1', plain,
% 0.24/0.53      (![X33 : $i, X34 : $i]:
% 0.24/0.53         (~ (m1_orders_1 @ X33 @ (k1_orders_1 @ (u1_struct_0 @ X34)))
% 0.24/0.53          | (m2_orders_2 @ 
% 0.24/0.53             (k1_tarski @ (k1_funct_1 @ X33 @ (u1_struct_0 @ X34))) @ X34 @ X33)
% 0.24/0.53          | ~ (l1_orders_2 @ X34)
% 0.24/0.53          | ~ (v5_orders_2 @ X34)
% 0.24/0.53          | ~ (v4_orders_2 @ X34)
% 0.24/0.53          | ~ (v3_orders_2 @ X34)
% 0.24/0.53          | (v2_struct_0 @ X34))),
% 0.24/0.53      inference('cnf', [status(esa)], [t78_orders_2])).
% 0.24/0.53  thf('2', plain,
% 0.24/0.53      (((v2_struct_0 @ sk_A)
% 0.24/0.53        | ~ (v3_orders_2 @ sk_A)
% 0.24/0.53        | ~ (v4_orders_2 @ sk_A)
% 0.24/0.53        | ~ (v5_orders_2 @ sk_A)
% 0.24/0.53        | ~ (l1_orders_2 @ sk_A)
% 0.24/0.53        | (m2_orders_2 @ 
% 0.24/0.53           (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ sk_A @ 
% 0.24/0.53           sk_B))),
% 0.24/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.53  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('7', plain,
% 0.24/0.53      (((v2_struct_0 @ sk_A)
% 0.24/0.53        | (m2_orders_2 @ 
% 0.24/0.53           (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ sk_A @ 
% 0.24/0.53           sk_B))),
% 0.24/0.53      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.24/0.53  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('9', plain,
% 0.24/0.53      ((m2_orders_2 @ 
% 0.24/0.53        (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ sk_A @ sk_B)),
% 0.24/0.53      inference('clc', [status(thm)], ['7', '8'])).
% 0.24/0.53  thf('10', plain,
% 0.24/0.53      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(d17_orders_2, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.24/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.24/0.53       ( ![B:$i]:
% 0.24/0.53         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53           ( ![C:$i]:
% 0.24/0.53             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.24/0.53               ( ![D:$i]:
% 0.24/0.53                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.24/0.53  thf('11', plain,
% 0.24/0.53      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.24/0.53         (~ (m1_orders_1 @ X27 @ (k1_orders_1 @ (u1_struct_0 @ X28)))
% 0.24/0.53          | ((X29) != (k4_orders_2 @ X28 @ X27))
% 0.24/0.53          | (r2_hidden @ X30 @ X29)
% 0.24/0.53          | ~ (m2_orders_2 @ X30 @ X28 @ X27)
% 0.24/0.53          | ~ (l1_orders_2 @ X28)
% 0.24/0.53          | ~ (v5_orders_2 @ X28)
% 0.24/0.53          | ~ (v4_orders_2 @ X28)
% 0.24/0.53          | ~ (v3_orders_2 @ X28)
% 0.24/0.53          | (v2_struct_0 @ X28))),
% 0.24/0.53      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.24/0.53  thf('12', plain,
% 0.24/0.53      (![X27 : $i, X28 : $i, X30 : $i]:
% 0.24/0.53         ((v2_struct_0 @ X28)
% 0.24/0.53          | ~ (v3_orders_2 @ X28)
% 0.24/0.53          | ~ (v4_orders_2 @ X28)
% 0.24/0.53          | ~ (v5_orders_2 @ X28)
% 0.24/0.53          | ~ (l1_orders_2 @ X28)
% 0.24/0.53          | ~ (m2_orders_2 @ X30 @ X28 @ X27)
% 0.24/0.53          | (r2_hidden @ X30 @ (k4_orders_2 @ X28 @ X27))
% 0.24/0.53          | ~ (m1_orders_1 @ X27 @ (k1_orders_1 @ (u1_struct_0 @ X28))))),
% 0.24/0.53      inference('simplify', [status(thm)], ['11'])).
% 0.24/0.53  thf('13', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B))
% 0.24/0.53          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.24/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.24/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.24/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.24/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.24/0.53          | (v2_struct_0 @ sk_A))),
% 0.24/0.53      inference('sup-', [status(thm)], ['10', '12'])).
% 0.24/0.53  thf('14', plain, ((l1_orders_2 @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('15', plain, ((v5_orders_2 @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('16', plain, ((v4_orders_2 @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('17', plain, ((v3_orders_2 @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('18', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B))
% 0.24/0.53          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.24/0.53          | (v2_struct_0 @ sk_A))),
% 0.24/0.53      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.24/0.53  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('20', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.24/0.53          | (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B)))),
% 0.24/0.53      inference('clc', [status(thm)], ['18', '19'])).
% 0.24/0.53  thf('21', plain,
% 0.24/0.53      ((r2_hidden @ (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.24/0.53        (k4_orders_2 @ sk_A @ sk_B))),
% 0.24/0.53      inference('sup-', [status(thm)], ['9', '20'])).
% 0.24/0.53  thf(l1_zfmisc_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.24/0.53  thf('22', plain,
% 0.24/0.53      (![X19 : $i, X21 : $i]:
% 0.24/0.53         ((r1_tarski @ (k1_tarski @ X19) @ X21) | ~ (r2_hidden @ X19 @ X21))),
% 0.24/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.24/0.53  thf('23', plain,
% 0.24/0.53      ((r1_tarski @ 
% 0.24/0.53        (k1_tarski @ (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)))) @ 
% 0.24/0.53        (k4_orders_2 @ sk_A @ sk_B))),
% 0.24/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.24/0.53  thf(t95_zfmisc_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( r1_tarski @ A @ B ) =>
% 0.24/0.53       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.24/0.53  thf('24', plain,
% 0.24/0.53      (![X23 : $i, X24 : $i]:
% 0.24/0.53         ((r1_tarski @ (k3_tarski @ X23) @ (k3_tarski @ X24))
% 0.24/0.53          | ~ (r1_tarski @ X23 @ X24))),
% 0.24/0.53      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.24/0.53  thf('25', plain,
% 0.24/0.53      ((r1_tarski @ 
% 0.24/0.53        (k3_tarski @ 
% 0.24/0.53         (k1_tarski @ (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))))) @ 
% 0.24/0.53        (k3_tarski @ (k4_orders_2 @ sk_A @ sk_B)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.24/0.53  thf(t31_zfmisc_1, axiom,
% 0.24/0.53    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.24/0.53  thf('26', plain, (![X22 : $i]: ((k3_tarski @ (k1_tarski @ X22)) = (X22))),
% 0.24/0.53      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.24/0.53  thf('27', plain,
% 0.24/0.53      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('28', plain,
% 0.24/0.53      ((r1_tarski @ (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.24/0.53        k1_xboole_0)),
% 0.24/0.53      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.24/0.53  thf('29', plain,
% 0.24/0.53      (![X19 : $i, X20 : $i]:
% 0.24/0.53         ((r2_hidden @ X19 @ X20) | ~ (r1_tarski @ (k1_tarski @ X19) @ X20))),
% 0.24/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.24/0.53  thf('30', plain,
% 0.24/0.53      ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ k1_xboole_0)),
% 0.24/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.24/0.53  thf(t7_ordinal1, axiom,
% 0.24/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.53  thf('31', plain,
% 0.24/0.53      (![X25 : $i, X26 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X25 @ X26) | ~ (r1_tarski @ X26 @ X25))),
% 0.24/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.24/0.53  thf('32', plain,
% 0.24/0.53      (~ (r1_tarski @ k1_xboole_0 @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.24/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.24/0.53  thf('33', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.24/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.24/0.53  thf('34', plain, ($false), inference('demod', [status(thm)], ['32', '33'])).
% 0.24/0.53  
% 0.24/0.53  % SZS output end Refutation
% 0.24/0.53  
% 0.24/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
