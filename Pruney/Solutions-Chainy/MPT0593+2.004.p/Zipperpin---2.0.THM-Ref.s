%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0Iw9g9JjhM

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  43 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :  152 ( 307 expanded)
%              Number of equality atoms :   27 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t197_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( ( ( k2_relat_1 @ A )
                = k1_xboole_0 )
              & ( ( k2_relat_1 @ B )
                = k1_xboole_0 ) )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( ( ( k2_relat_1 @ A )
                  = k1_xboole_0 )
                & ( ( k2_relat_1 @ B )
                  = k1_xboole_0 ) )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t197_relat_1])).

thf('0',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( ( k3_xboole_0 @ X4 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X4 ) @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('2',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['2','4','5','6'])).

thf('8',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X4: $i] :
      ( ( ( k3_xboole_0 @ X4 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X4 ) @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('10',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0Iw9g9JjhM
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.44  % Solved by: fo/fo7.sh
% 0.21/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.44  % done 10 iterations in 0.008s
% 0.21/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.44  % SZS output start Refutation
% 0.21/0.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.44  thf(t197_relat_1, conjecture,
% 0.21/0.44    (![A:$i]:
% 0.21/0.44     ( ( v1_relat_1 @ A ) =>
% 0.21/0.44       ( ![B:$i]:
% 0.21/0.44         ( ( v1_relat_1 @ B ) =>
% 0.21/0.44           ( ( ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.44               ( ( k2_relat_1 @ B ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.44             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.44    (~( ![A:$i]:
% 0.21/0.44        ( ( v1_relat_1 @ A ) =>
% 0.21/0.44          ( ![B:$i]:
% 0.21/0.44            ( ( v1_relat_1 @ B ) =>
% 0.21/0.44              ( ( ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.44                  ( ( k2_relat_1 @ B ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.44                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.21/0.44    inference('cnf.neg', [status(esa)], [t197_relat_1])).
% 0.21/0.44  thf('0', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf(t22_relat_1, axiom,
% 0.21/0.44    (![A:$i]:
% 0.21/0.44     ( ( v1_relat_1 @ A ) =>
% 0.21/0.44       ( ( k3_xboole_0 @
% 0.21/0.44           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.21/0.44         ( A ) ) ))).
% 0.21/0.44  thf('1', plain,
% 0.21/0.44      (![X4 : $i]:
% 0.21/0.44         (((k3_xboole_0 @ X4 @ 
% 0.21/0.44            (k2_zfmisc_1 @ (k1_relat_1 @ X4) @ (k2_relat_1 @ X4))) = (X4))
% 0.21/0.44          | ~ (v1_relat_1 @ X4))),
% 0.21/0.44      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.21/0.44  thf('2', plain,
% 0.21/0.44      ((((k3_xboole_0 @ sk_A @ 
% 0.21/0.44          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0)) = (sk_A))
% 0.21/0.44        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.44      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.44  thf(t113_zfmisc_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.44       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.44  thf('3', plain,
% 0.21/0.44      (![X2 : $i, X3 : $i]:
% 0.21/0.44         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.44  thf('4', plain,
% 0.21/0.44      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.44      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.44  thf(t2_boole, axiom,
% 0.21/0.44    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.44  thf('5', plain,
% 0.21/0.44      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.44      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.44  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('7', plain, (((k1_xboole_0) = (sk_A))),
% 0.21/0.44      inference('demod', [status(thm)], ['2', '4', '5', '6'])).
% 0.21/0.44  thf('8', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('9', plain,
% 0.21/0.44      (![X4 : $i]:
% 0.21/0.44         (((k3_xboole_0 @ X4 @ 
% 0.21/0.44            (k2_zfmisc_1 @ (k1_relat_1 @ X4) @ (k2_relat_1 @ X4))) = (X4))
% 0.21/0.44          | ~ (v1_relat_1 @ X4))),
% 0.21/0.44      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.21/0.44  thf('10', plain,
% 0.21/0.44      ((((k3_xboole_0 @ sk_B @ 
% 0.21/0.44          (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ k1_xboole_0)) = (sk_B))
% 0.21/0.44        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.44      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.44  thf('11', plain,
% 0.21/0.44      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.44      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.44  thf('12', plain,
% 0.21/0.44      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.44      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.44  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('14', plain, (((k1_xboole_0) = (sk_B))),
% 0.21/0.44      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.21/0.44  thf('15', plain, (((sk_A) = (sk_B))),
% 0.21/0.44      inference('sup+', [status(thm)], ['7', '14'])).
% 0.21/0.44  thf('16', plain, (((sk_A) != (sk_B))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('17', plain, ($false),
% 0.21/0.44      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.21/0.44  
% 0.21/0.44  % SZS output end Refutation
% 0.21/0.44  
% 0.21/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
