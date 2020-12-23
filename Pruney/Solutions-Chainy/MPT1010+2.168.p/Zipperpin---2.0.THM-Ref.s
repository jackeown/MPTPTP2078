%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.54bpqHMLQN

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  56 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  316 ( 492 expanded)
%              Number of equality atoms :   33 (  41 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X23 @ X20 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
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
    ! [X10: $i,X11: $i] :
      ( ( X11 != X10 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X10 ) )
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('8',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X10 ) )
     != ( k1_tarski @ X10 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t208_relat_1,axiom,(
    ! [A: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ A ) ) )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X17: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X17 @ X17 ) ) )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t208_relat_1])).

thf(t32_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X18 @ X19 ) ) )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t32_relat_1])).

thf('11',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t75_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) )
        = k1_xboole_0 )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ ( k2_tarski @ X13 @ X16 ) )
        = k1_xboole_0 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t75_zfmisc_1])).

thf('13',plain,(
    ! [X13: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X13 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X10: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X10 ) ) ),
    inference(demod,[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['6','15'])).

thf('17',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.54bpqHMLQN
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 41 iterations in 0.016s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.47  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.47  thf(t65_funct_2, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.47         ( m1_subset_1 @
% 0.21/0.47           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.47       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.47            ( m1_subset_1 @
% 0.21/0.47              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.47          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.21/0.47  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_D @ 
% 0.21/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t7_funct_2, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.47       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.47         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.47           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X20 @ X21)
% 0.21/0.47          | ((X22) = (k1_xboole_0))
% 0.21/0.47          | ~ (v1_funct_1 @ X23)
% 0.21/0.47          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.21/0.47          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.21/0.47          | (r2_hidden @ (k1_funct_1 @ X23 @ X20) @ X22))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.47          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.47          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.47          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.47          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.47  thf(t20_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.47         ( k1_tarski @ A ) ) <=>
% 0.21/0.47       ( ( A ) != ( B ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i]:
% 0.21/0.47         (((X11) != (X10))
% 0.21/0.47          | ((k4_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X10))
% 0.21/0.47              != (k1_tarski @ X11)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X10 : $i]:
% 0.21/0.47         ((k4_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X10))
% 0.21/0.47           != (k1_tarski @ X10))),
% 0.21/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.47  thf(t208_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ A ) ) ) =
% 0.21/0.47       ( k1_tarski @ A ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X17 : $i]:
% 0.21/0.47         ((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X17 @ X17)))
% 0.21/0.47           = (k1_tarski @ X17))),
% 0.21/0.47      inference('cnf', [status(esa)], [t208_relat_1])).
% 0.21/0.47  thf(t32_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =
% 0.21/0.47       ( k2_tarski @ A @ B ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X18 : $i, X19 : $i]:
% 0.21/0.47         ((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X18 @ X19)))
% 0.21/0.47           = (k2_tarski @ X18 @ X19))),
% 0.21/0.47      inference('cnf', [status(esa)], [t32_relat_1])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.21/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf(t75_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.47       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.21/0.47            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.21/0.47         (((k4_xboole_0 @ X15 @ (k2_tarski @ X13 @ X16)) = (k1_xboole_0))
% 0.21/0.47          | ((X15) != (k1_tarski @ X13)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t75_zfmisc_1])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X13 : $i, X16 : $i]:
% 0.21/0.47         ((k4_xboole_0 @ (k1_tarski @ X13) @ (k2_tarski @ X13 @ X16))
% 0.21/0.47           = (k1_xboole_0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['11', '13'])).
% 0.21/0.47  thf('15', plain, (![X10 : $i]: ((k1_xboole_0) != (k1_tarski @ X10))),
% 0.21/0.47      inference('demod', [status(thm)], ['8', '14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.47          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('clc', [status(thm)], ['6', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '16'])).
% 0.21/0.47  thf(d1_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i, X3 : $i]:
% 0.21/0.47         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.47  thf('20', plain, (((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.47  thf('21', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('22', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
