%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DMs2gFM2ho

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:26 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 144 expanded)
%              Number of leaves         :   28 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  530 (1629 expanded)
%              Number of equality atoms :   30 (  82 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

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
    ! [X44: $i,X45: $i] :
      ( ~ ( l1_orders_2 @ X44 )
      | ~ ( v5_orders_2 @ X44 )
      | ~ ( v4_orders_2 @ X44 )
      | ~ ( v3_orders_2 @ X44 )
      | ( v2_struct_0 @ X44 )
      | ~ ( m1_orders_1 @ X45 @ ( k1_orders_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( m2_orders_2 @ ( sk_C @ X45 @ X44 ) @ X44 @ X45 ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_orders_1 @ X46 @ ( k1_orders_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X46 @ ( u1_struct_0 @ X47 ) ) @ X48 )
      | ~ ( m2_orders_2 @ X48 @ X47 @ X46 )
      | ~ ( l1_orders_2 @ X47 )
      | ~ ( v5_orders_2 @ X47 )
      | ~ ( v4_orders_2 @ X47 )
      | ~ ( v3_orders_2 @ X47 )
      | ( v2_struct_0 @ X47 ) ) ),
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

thf('21',plain,(
    m2_orders_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_orders_1 @ X37 @ ( k1_orders_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( X39
       != ( k4_orders_2 @ X38 @ X37 ) )
      | ( r2_hidden @ X40 @ X39 )
      | ~ ( m2_orders_2 @ X40 @ X38 @ X37 )
      | ~ ( l1_orders_2 @ X38 )
      | ~ ( v5_orders_2 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ~ ( v3_orders_2 @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('24',plain,(
    ! [X37: $i,X38: $i,X40: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v3_orders_2 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ~ ( v5_orders_2 @ X38 )
      | ~ ( l1_orders_2 @ X38 )
      | ~ ( m2_orders_2 @ X40 @ X38 @ X37 )
      | ( r2_hidden @ X40 @ ( k4_orders_2 @ X38 @ X37 ) )
      | ~ ( m1_orders_1 @ X37 @ ( k1_orders_1 @ ( u1_struct_0 @ X38 ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('35',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('36',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf(t91_orders_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( ( k3_tarski @ A )
           != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( B != k1_xboole_0 )
                & ( r2_hidden @ B @ A ) ) )
      & ~ ( ? [B: $i] :
              ( ( r2_hidden @ B @ A )
              & ( B != k1_xboole_0 ) )
          & ( ( k3_tarski @ A )
            = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( r2_hidden @ X49 @ X50 )
      | ( ( k3_tarski @ X50 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('38',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('39',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('40',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X49 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X49 @ X50 )
      | ( ( k3_tarski @ X50 )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( X0 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( sk_C @ sk_B_1 @ sk_A )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['20','43'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('45',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('46',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('47',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('48',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X2 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('49',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ( ( k4_xboole_0 @ X32 @ ( k1_tarski @ X31 ) )
       != X32 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    $false ),
    inference('sup-',[status(thm)],['44','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DMs2gFM2ho
% 0.17/0.37  % Computer   : n024.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 19:50:21 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.24/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.52  % Solved by: fo/fo7.sh
% 0.24/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.52  % done 69 iterations in 0.034s
% 0.24/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.52  % SZS output start Refutation
% 0.24/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.24/0.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.24/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.24/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.52  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.24/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.52  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.24/0.52  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.24/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.24/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.52  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.24/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.24/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.52  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.24/0.52  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.24/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.52  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.24/0.52  thf(t87_orders_2, conjecture,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.24/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.24/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.52    (~( ![A:$i]:
% 0.24/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.24/0.52            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.24/0.52          ( ![B:$i]:
% 0.24/0.52            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.24/0.52    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.24/0.52  thf('0', plain,
% 0.24/0.52      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(existence_m2_orders_2, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.24/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.24/0.52         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.52       ( ?[C:$i]: ( m2_orders_2 @ C @ A @ B ) ) ))).
% 0.24/0.52  thf('1', plain,
% 0.24/0.52      (![X44 : $i, X45 : $i]:
% 0.24/0.52         (~ (l1_orders_2 @ X44)
% 0.24/0.52          | ~ (v5_orders_2 @ X44)
% 0.24/0.52          | ~ (v4_orders_2 @ X44)
% 0.24/0.52          | ~ (v3_orders_2 @ X44)
% 0.24/0.52          | (v2_struct_0 @ X44)
% 0.24/0.52          | ~ (m1_orders_1 @ X45 @ (k1_orders_1 @ (u1_struct_0 @ X44)))
% 0.24/0.52          | (m2_orders_2 @ (sk_C @ X45 @ X44) @ X44 @ X45))),
% 0.24/0.52      inference('cnf', [status(esa)], [existence_m2_orders_2])).
% 0.24/0.52  thf('2', plain,
% 0.24/0.52      (((m2_orders_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.24/0.52        | (v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (v3_orders_2 @ sk_A)
% 0.24/0.52        | ~ (v4_orders_2 @ sk_A)
% 0.24/0.52        | ~ (v5_orders_2 @ sk_A)
% 0.24/0.52        | ~ (l1_orders_2 @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.52  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('7', plain,
% 0.24/0.52      (((m2_orders_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.24/0.52        | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.24/0.52  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('9', plain, ((m2_orders_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.24/0.52      inference('clc', [status(thm)], ['7', '8'])).
% 0.24/0.52  thf('10', plain,
% 0.24/0.52      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(t79_orders_2, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.24/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52           ( ![C:$i]:
% 0.24/0.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.24/0.52               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.24/0.52  thf('11', plain,
% 0.24/0.52      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.24/0.52         (~ (m1_orders_1 @ X46 @ (k1_orders_1 @ (u1_struct_0 @ X47)))
% 0.24/0.52          | (r2_hidden @ (k1_funct_1 @ X46 @ (u1_struct_0 @ X47)) @ X48)
% 0.24/0.52          | ~ (m2_orders_2 @ X48 @ X47 @ X46)
% 0.24/0.52          | ~ (l1_orders_2 @ X47)
% 0.24/0.52          | ~ (v5_orders_2 @ X47)
% 0.24/0.52          | ~ (v4_orders_2 @ X47)
% 0.24/0.52          | ~ (v3_orders_2 @ X47)
% 0.24/0.52          | (v2_struct_0 @ X47))),
% 0.24/0.52      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.24/0.52  thf('12', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((v2_struct_0 @ sk_A)
% 0.24/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.24/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.24/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.24/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.24/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.24/0.52          | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.24/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.52  thf('13', plain, ((v3_orders_2 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('14', plain, ((v4_orders_2 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('15', plain, ((v5_orders_2 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('16', plain, ((l1_orders_2 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('17', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((v2_struct_0 @ sk_A)
% 0.24/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.24/0.52          | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.24/0.52      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.24/0.52  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('19', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.24/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.24/0.52      inference('clc', [status(thm)], ['17', '18'])).
% 0.24/0.52  thf('20', plain,
% 0.24/0.52      ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.24/0.52        (sk_C @ sk_B_1 @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['9', '19'])).
% 0.24/0.52  thf('21', plain, ((m2_orders_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.24/0.52      inference('clc', [status(thm)], ['7', '8'])).
% 0.24/0.52  thf('22', plain,
% 0.24/0.52      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(d17_orders_2, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.24/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52           ( ![C:$i]:
% 0.24/0.52             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.24/0.52               ( ![D:$i]:
% 0.24/0.52                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.24/0.52  thf('23', plain,
% 0.24/0.52      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.24/0.52         (~ (m1_orders_1 @ X37 @ (k1_orders_1 @ (u1_struct_0 @ X38)))
% 0.24/0.52          | ((X39) != (k4_orders_2 @ X38 @ X37))
% 0.24/0.52          | (r2_hidden @ X40 @ X39)
% 0.24/0.52          | ~ (m2_orders_2 @ X40 @ X38 @ X37)
% 0.24/0.52          | ~ (l1_orders_2 @ X38)
% 0.24/0.52          | ~ (v5_orders_2 @ X38)
% 0.24/0.52          | ~ (v4_orders_2 @ X38)
% 0.24/0.52          | ~ (v3_orders_2 @ X38)
% 0.24/0.52          | (v2_struct_0 @ X38))),
% 0.24/0.52      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.24/0.52  thf('24', plain,
% 0.24/0.52      (![X37 : $i, X38 : $i, X40 : $i]:
% 0.24/0.52         ((v2_struct_0 @ X38)
% 0.24/0.52          | ~ (v3_orders_2 @ X38)
% 0.24/0.52          | ~ (v4_orders_2 @ X38)
% 0.24/0.52          | ~ (v5_orders_2 @ X38)
% 0.24/0.52          | ~ (l1_orders_2 @ X38)
% 0.24/0.52          | ~ (m2_orders_2 @ X40 @ X38 @ X37)
% 0.24/0.52          | (r2_hidden @ X40 @ (k4_orders_2 @ X38 @ X37))
% 0.24/0.52          | ~ (m1_orders_1 @ X37 @ (k1_orders_1 @ (u1_struct_0 @ X38))))),
% 0.24/0.52      inference('simplify', [status(thm)], ['23'])).
% 0.24/0.52  thf('25', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.24/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.24/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.24/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.24/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.24/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.24/0.52          | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['22', '24'])).
% 0.24/0.52  thf('26', plain, ((l1_orders_2 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('27', plain, ((v5_orders_2 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('28', plain, ((v4_orders_2 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('29', plain, ((v3_orders_2 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('30', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.24/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.24/0.52          | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.24/0.52  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('32', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.24/0.52          | (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.24/0.52      inference('clc', [status(thm)], ['30', '31'])).
% 0.24/0.52  thf('33', plain,
% 0.24/0.52      ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.24/0.52      inference('sup-', [status(thm)], ['21', '32'])).
% 0.24/0.52  thf('34', plain,
% 0.24/0.52      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.24/0.52  thf('35', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.24/0.52  thf('36', plain,
% 0.24/0.52      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (o_0_0_xboole_0))),
% 0.24/0.52      inference('demod', [status(thm)], ['34', '35'])).
% 0.24/0.52  thf(t91_orders_1, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.52            ( ![B:$i]:
% 0.24/0.52              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 0.24/0.52       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.24/0.52            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.24/0.52  thf('37', plain,
% 0.24/0.52      (![X49 : $i, X50 : $i]:
% 0.24/0.52         (((X49) = (k1_xboole_0))
% 0.24/0.52          | ~ (r2_hidden @ X49 @ X50)
% 0.24/0.52          | ((k3_tarski @ X50) != (k1_xboole_0)))),
% 0.24/0.52      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.24/0.52  thf('38', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.24/0.52  thf('39', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.24/0.52  thf('40', plain,
% 0.24/0.52      (![X49 : $i, X50 : $i]:
% 0.24/0.52         (((X49) = (o_0_0_xboole_0))
% 0.24/0.52          | ~ (r2_hidden @ X49 @ X50)
% 0.24/0.52          | ((k3_tarski @ X50) != (o_0_0_xboole_0)))),
% 0.24/0.52      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.24/0.52  thf('41', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.24/0.52          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.24/0.52          | ((X0) = (o_0_0_xboole_0)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['36', '40'])).
% 0.24/0.52  thf('42', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (((X0) = (o_0_0_xboole_0))
% 0.24/0.52          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.24/0.52      inference('simplify', [status(thm)], ['41'])).
% 0.24/0.52  thf('43', plain, (((sk_C @ sk_B_1 @ sk_A) = (o_0_0_xboole_0))),
% 0.24/0.52      inference('sup-', [status(thm)], ['33', '42'])).
% 0.24/0.52  thf('44', plain,
% 0.24/0.52      ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.24/0.52        o_0_0_xboole_0)),
% 0.24/0.52      inference('demod', [status(thm)], ['20', '43'])).
% 0.24/0.52  thf(t4_boole, axiom,
% 0.24/0.52    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.24/0.52  thf('45', plain,
% 0.24/0.52      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [t4_boole])).
% 0.24/0.52  thf('46', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.24/0.52  thf('47', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.24/0.52  thf('48', plain,
% 0.24/0.52      (![X2 : $i]: ((k4_xboole_0 @ o_0_0_xboole_0 @ X2) = (o_0_0_xboole_0))),
% 0.24/0.52      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.24/0.52  thf(t65_zfmisc_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.24/0.52       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.24/0.52  thf('49', plain,
% 0.24/0.52      (![X31 : $i, X32 : $i]:
% 0.24/0.52         (~ (r2_hidden @ X31 @ X32)
% 0.24/0.52          | ((k4_xboole_0 @ X32 @ (k1_tarski @ X31)) != (X32)))),
% 0.24/0.52      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.24/0.52  thf('50', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.24/0.52          | ~ (r2_hidden @ X0 @ o_0_0_xboole_0))),
% 0.24/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.24/0.52  thf('51', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ o_0_0_xboole_0)),
% 0.24/0.52      inference('simplify', [status(thm)], ['50'])).
% 0.24/0.52  thf('52', plain, ($false), inference('sup-', [status(thm)], ['44', '51'])).
% 0.24/0.52  
% 0.24/0.52  % SZS output end Refutation
% 0.24/0.52  
% 0.24/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
