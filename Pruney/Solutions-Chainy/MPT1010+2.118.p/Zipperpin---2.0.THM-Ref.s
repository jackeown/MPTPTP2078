%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J73DyvvIf6

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:29 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   48 (  56 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  307 ( 483 expanded)
%              Number of equality atoms :   32 (  40 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('2',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X43 @ X44 )
      | ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X46 @ X43 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('7',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X41 != X40 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X41 ) @ ( k1_tarski @ X40 ) )
       != ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('8',plain,(
    ! [X40: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X40 ) @ ( k1_tarski @ X40 ) )
     != ( k1_tarski @ X40 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X40: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X40 ) ) ),
    inference(demod,[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('15',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ( X10 = X9 )
      | ( X10 = X6 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('18',plain,(
    ! [X6: $i,X9: $i,X10: $i] :
      ( ( X10 = X6 )
      | ( X10 = X9 )
      | ~ ( r2_hidden @ X10 @ ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( k1_funct_1 @ sk_D_1 @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ( k1_funct_1 @ sk_D_1 @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J73DyvvIf6
% 0.17/0.38  % Computer   : n021.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 20:15:20 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 41 iterations in 0.021s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.24/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.24/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.24/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.51  thf(t65_funct_2, conjecture,
% 0.24/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.24/0.51         ( m1_subset_1 @
% 0.24/0.51           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.24/0.51       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.51        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.24/0.51            ( m1_subset_1 @
% 0.24/0.51              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.24/0.51          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.24/0.51  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('1', plain,
% 0.24/0.51      ((m1_subset_1 @ sk_D_1 @ 
% 0.24/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(t7_funct_2, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.24/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.51       ( ( r2_hidden @ C @ A ) =>
% 0.24/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.24/0.51           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.24/0.51  thf('2', plain,
% 0.24/0.51      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X43 @ X44)
% 0.24/0.51          | ((X45) = (k1_xboole_0))
% 0.24/0.51          | ~ (v1_funct_1 @ X46)
% 0.24/0.51          | ~ (v1_funct_2 @ X46 @ X44 @ X45)
% 0.24/0.51          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.24/0.51          | (r2_hidden @ (k1_funct_1 @ X46 @ X43) @ X45))),
% 0.24/0.51      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.24/0.51  thf('3', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B))
% 0.24/0.51          | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.24/0.51          | ~ (v1_funct_1 @ sk_D_1)
% 0.24/0.51          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.24/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.51  thf('4', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('5', plain, ((v1_funct_1 @ sk_D_1)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('6', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B))
% 0.24/0.51          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.24/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.24/0.51      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.24/0.51  thf(t20_zfmisc_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.24/0.51         ( k1_tarski @ A ) ) <=>
% 0.24/0.51       ( ( A ) != ( B ) ) ))).
% 0.24/0.51  thf('7', plain,
% 0.24/0.51      (![X40 : $i, X41 : $i]:
% 0.24/0.51         (((X41) != (X40))
% 0.24/0.51          | ((k4_xboole_0 @ (k1_tarski @ X41) @ (k1_tarski @ X40))
% 0.24/0.51              != (k1_tarski @ X41)))),
% 0.24/0.51      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.24/0.51  thf('8', plain,
% 0.24/0.51      (![X40 : $i]:
% 0.24/0.51         ((k4_xboole_0 @ (k1_tarski @ X40) @ (k1_tarski @ X40))
% 0.24/0.51           != (k1_tarski @ X40))),
% 0.24/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.24/0.51  thf(d10_xboole_0, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.51  thf('9', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.24/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.51  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.24/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.24/0.51  thf(l32_xboole_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.51  thf('11', plain,
% 0.24/0.51      (![X3 : $i, X5 : $i]:
% 0.24/0.51         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.24/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.24/0.51  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.51  thf('13', plain, (![X40 : $i]: ((k1_xboole_0) != (k1_tarski @ X40))),
% 0.24/0.51      inference('demod', [status(thm)], ['8', '12'])).
% 0.24/0.51  thf('14', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X0 @ sk_A)
% 0.24/0.51          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B)))),
% 0.24/0.51      inference('clc', [status(thm)], ['6', '13'])).
% 0.24/0.51  thf('15', plain,
% 0.24/0.51      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C) @ (k1_tarski @ sk_B))),
% 0.24/0.51      inference('sup-', [status(thm)], ['0', '14'])).
% 0.24/0.51  thf(t69_enumset1, axiom,
% 0.24/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.24/0.51  thf('16', plain,
% 0.24/0.51      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.24/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.51  thf(d2_tarski, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i]:
% 0.24/0.51     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.24/0.51       ( ![D:$i]:
% 0.24/0.51         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.24/0.51  thf('17', plain,
% 0.24/0.51      (![X6 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X10 @ X8)
% 0.24/0.51          | ((X10) = (X9))
% 0.24/0.51          | ((X10) = (X6))
% 0.24/0.51          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 0.24/0.51      inference('cnf', [status(esa)], [d2_tarski])).
% 0.24/0.51  thf('18', plain,
% 0.24/0.51      (![X6 : $i, X9 : $i, X10 : $i]:
% 0.24/0.51         (((X10) = (X6))
% 0.24/0.51          | ((X10) = (X9))
% 0.24/0.51          | ~ (r2_hidden @ X10 @ (k2_tarski @ X9 @ X6)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['17'])).
% 0.24/0.51  thf('19', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['16', '18'])).
% 0.24/0.51  thf('20', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['19'])).
% 0.24/0.51  thf('21', plain, (((k1_funct_1 @ sk_D_1 @ sk_C) = (sk_B))),
% 0.24/0.51      inference('sup-', [status(thm)], ['15', '20'])).
% 0.24/0.51  thf('22', plain, (((k1_funct_1 @ sk_D_1 @ sk_C) != (sk_B))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('23', plain, ($false),
% 0.24/0.51      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
