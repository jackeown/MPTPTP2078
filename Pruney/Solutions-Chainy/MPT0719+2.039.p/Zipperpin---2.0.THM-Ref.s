%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IfHSdsB332

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  56 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  238 ( 276 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X10 ) @ ( k1_relat_1 @ X9 ) )
      | ( v5_funct_1 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('3',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X13: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('7',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('8',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','5','8'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) @ X6 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X7: $i] :
      ( ( ( k2_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf(t174_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( v5_funct_1 @ k1_xboole_0 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( v5_funct_1 @ k1_xboole_0 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t174_funct_1])).

thf('21',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['22','23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IfHSdsB332
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:35:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 29 iterations in 0.010s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.20/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.47  thf(t60_relat_1, axiom,
% 0.20/0.47    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.47     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.47  thf('0', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.47  thf(d20_funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47           ( ( v5_funct_1 @ B @ A ) <=>
% 0.20/0.47             ( ![C:$i]:
% 0.20/0.47               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.47                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X9)
% 0.20/0.47          | ~ (v1_funct_1 @ X9)
% 0.20/0.47          | (r2_hidden @ (sk_C @ X9 @ X10) @ (k1_relat_1 @ X9))
% 0.20/0.47          | (v5_funct_1 @ X9 @ X10)
% 0.20/0.47          | ~ (v1_funct_1 @ X10)
% 0.20/0.47          | ~ (v1_relat_1 @ X10))),
% 0.20/0.47      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.47          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.47  thf('3', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.47  thf(fc3_funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.47       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.47  thf('4', plain, (![X13 : $i]: (v1_funct_1 @ (k6_relat_1 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.47  thf('5', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.47      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('6', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.47  thf('7', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.47  thf('8', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.47      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '5', '8'])).
% 0.20/0.47  thf(t194_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]:
% 0.20/0.47         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X5 @ X6)) @ X6)),
% 0.20/0.47      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.20/0.47  thf(t3_xboole_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf(t64_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.47         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X7 : $i]:
% 0.20/0.47         (((k2_relat_1 @ X7) != (k1_xboole_0))
% 0.20/0.47          | ((X7) = (k1_xboole_0))
% 0.20/0.47          | ~ (v1_relat_1 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.47          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 0.20/0.47          | ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf(fc6_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.47          | ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.47  thf(t152_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i]: ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ X1 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.20/0.47  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '19'])).
% 0.20/0.47  thf(t174_funct_1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.47       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.47          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.20/0.47  thf('21', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('22', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('24', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain, ($false),
% 0.20/0.47      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
