%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l7M1CFu74b

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  53 expanded)
%              Number of leaves         :   11 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  209 ( 408 expanded)
%              Number of equality atoms :   42 (  87 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t64_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( ( k1_relat_1 @ A )
              = k1_xboole_0 )
            | ( ( k2_relat_1 @ A )
              = k1_xboole_0 ) )
         => ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_relat_1])).

thf('0',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( ( k3_xboole_0 @ X4 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X4 ) @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('3',plain,
    ( ( ( ( k3_xboole_0 @ sk_A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) )
        = sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('5',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k1_xboole_0 = sk_A )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','5','6','7'])).

thf('9',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( $false
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    ! [X4: $i] :
      ( ( ( k3_xboole_0 @ X4 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X4 ) @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('13',plain,
    ( ( ( ( k3_xboole_0 @ sk_A @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_A ) ) )
        = sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k1_xboole_0 = sk_A )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','15','16','17'])).

thf('19',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ( k1_relat_1 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['10','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l7M1CFu74b
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:01:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 10 iterations in 0.010s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(t64_relat_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.47           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.47         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( v1_relat_1 @ A ) =>
% 0.21/0.47          ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.47              ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.47            ( ( A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t64_relat_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((((k1_relat_1 @ sk_A) = (k1_xboole_0))
% 0.21/0.47        | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((((k2_relat_1 @ sk_A) = (k1_xboole_0)))
% 0.21/0.47         <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf(t22_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ( k3_xboole_0 @
% 0.21/0.47           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.21/0.47         ( A ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X4 : $i]:
% 0.21/0.47         (((k3_xboole_0 @ X4 @ 
% 0.21/0.47            (k2_zfmisc_1 @ (k1_relat_1 @ X4) @ (k2_relat_1 @ X4))) = (X4))
% 0.21/0.47          | ~ (v1_relat_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (((((k3_xboole_0 @ sk_A @ 
% 0.21/0.47           (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0)) = (sk_A))
% 0.21/0.47         | ~ (v1_relat_1 @ sk_A))) <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(t113_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.47  thf(t2_boole, axiom,
% 0.21/0.47    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.47  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      ((((k1_xboole_0) = (sk_A))) <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '5', '6', '7'])).
% 0.21/0.47  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain, (($false) <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      ((((k1_relat_1 @ sk_A) = (k1_xboole_0)))
% 0.21/0.47         <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X4 : $i]:
% 0.21/0.47         (((k3_xboole_0 @ X4 @ 
% 0.21/0.47            (k2_zfmisc_1 @ (k1_relat_1 @ X4) @ (k2_relat_1 @ X4))) = (X4))
% 0.21/0.47          | ~ (v1_relat_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (((((k3_xboole_0 @ sk_A @ 
% 0.21/0.47           (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_A))) = (sk_A))
% 0.21/0.47         | ~ (v1_relat_1 @ sk_A))) <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.47  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      ((((k1_xboole_0) = (sk_A))) <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '15', '16', '17'])).
% 0.21/0.47  thf('19', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('20', plain, (~ (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      ((((k2_relat_1 @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.47       (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('22', plain, ((((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('23', plain, ($false),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['10', '22'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
