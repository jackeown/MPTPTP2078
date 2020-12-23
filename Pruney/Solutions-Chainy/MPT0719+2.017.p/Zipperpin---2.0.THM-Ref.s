%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qyRsQifUbx

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:28 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  250 ( 294 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,
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

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ ( k1_relat_1 @ X7 ) )
      | ( v5_funct_1 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf('23',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v5_funct_1 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['25','26','27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qyRsQifUbx
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 261 iterations in 0.142s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.59  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.59  thf(cc1_funct_1, axiom,
% 0.41/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.41/0.59  thf('0', plain, (![X6 : $i]: ((v1_funct_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.41/0.59  thf(cc1_relat_1, axiom,
% 0.41/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.41/0.59  thf('1', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.41/0.59  thf(t60_relat_1, axiom,
% 0.41/0.59    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.41/0.59     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.41/0.59  thf('2', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.41/0.59  thf(d20_funct_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.59           ( ( v5_funct_1 @ B @ A ) <=>
% 0.41/0.59             ( ![C:$i]:
% 0.41/0.59               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.41/0.59                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      (![X7 : $i, X8 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X7)
% 0.41/0.59          | ~ (v1_funct_1 @ X7)
% 0.41/0.59          | (r2_hidden @ (sk_C @ X7 @ X8) @ (k1_relat_1 @ X7))
% 0.41/0.59          | (v5_funct_1 @ X7 @ X8)
% 0.41/0.59          | ~ (v1_funct_1 @ X8)
% 0.41/0.59          | ~ (v1_relat_1 @ X8))),
% 0.41/0.59      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.41/0.59  thf(l13_xboole_0, axiom,
% 0.41/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.41/0.59  thf(fc3_zfmisc_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X1 : $i, X2 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X2)) | ~ (v1_xboole_0 @ X2))),
% 0.41/0.59      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.59  thf(t152_zfmisc_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X2))),
% 0.41/0.59      inference('sup-', [status(thm)], ['4', '9'])).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.59      inference('condensation', [status(thm)], ['10'])).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X1)
% 0.41/0.59          | ~ (v1_funct_1 @ X1)
% 0.41/0.59          | (v5_funct_1 @ X0 @ X1)
% 0.41/0.59          | ~ (v1_funct_1 @ X0)
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['3', '11'])).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.41/0.59          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.41/0.59          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.41/0.59          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.41/0.59          | ~ (v1_funct_1 @ X0)
% 0.41/0.59          | ~ (v1_relat_1 @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['2', '12'])).
% 0.41/0.59  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.41/0.59  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ k1_xboole_0)
% 0.41/0.59          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.41/0.59          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.41/0.59          | ~ (v1_funct_1 @ X0)
% 0.41/0.59          | ~ (v1_relat_1 @ X0))),
% 0.41/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | ~ (v1_funct_1 @ X0)
% 0.41/0.59          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.41/0.59          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['1', '15'])).
% 0.41/0.59  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X0)
% 0.41/0.59          | ~ (v1_funct_1 @ X0)
% 0.41/0.59          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.41/0.59          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.41/0.59          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.41/0.59          | ~ (v1_funct_1 @ X0)
% 0.41/0.59          | ~ (v1_relat_1 @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['0', '18'])).
% 0.41/0.59  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.41/0.59          | ~ (v1_funct_1 @ X0)
% 0.41/0.59          | ~ (v1_relat_1 @ X0))),
% 0.41/0.59      inference('demod', [status(thm)], ['19', '20'])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.41/0.59  thf(t174_funct_1, conjecture,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.59       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i]:
% 0.41/0.59        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.59          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.41/0.59  thf('23', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      (![X0 : $i]: (~ (v5_funct_1 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      ((~ (v1_relat_1 @ sk_A)
% 0.41/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.41/0.59        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['21', '24'])).
% 0.41/0.59  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('27', plain, ((v1_funct_1 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.59  thf('29', plain, ($false),
% 0.41/0.59      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
