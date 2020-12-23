%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KzXAPmneff

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:30 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  228 ( 278 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X7 ) @ ( k1_relat_1 @ X6 ) )
      | ( v5_funct_1 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X10: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('7',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
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

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
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

thf('22',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v5_funct_1 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['24','25','26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KzXAPmneff
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:10:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 187 iterations in 0.083s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.37/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.37/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.54  thf(t60_relat_1, axiom,
% 0.37/0.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.37/0.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.54  thf('0', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.54  thf(d20_funct_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.54           ( ( v5_funct_1 @ B @ A ) <=>
% 0.37/0.54             ( ![C:$i]:
% 0.37/0.54               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.37/0.54                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      (![X6 : $i, X7 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X6)
% 0.37/0.54          | ~ (v1_funct_1 @ X6)
% 0.37/0.54          | (r2_hidden @ (sk_C @ X6 @ X7) @ (k1_relat_1 @ X6))
% 0.37/0.54          | (v5_funct_1 @ X6 @ X7)
% 0.37/0.54          | ~ (v1_funct_1 @ X7)
% 0.37/0.54          | ~ (v1_relat_1 @ X7))),
% 0.37/0.54      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | ~ (v1_funct_1 @ X0)
% 0.37/0.54          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.37/0.54          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.37/0.54          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['0', '1'])).
% 0.37/0.54  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.37/0.54  thf('3', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.37/0.54  thf(fc3_funct_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.37/0.54       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.37/0.54  thf('4', plain, (![X10 : $i]: (v1_funct_1 @ (k6_relat_1 @ X10))),
% 0.37/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.54  thf('5', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.37/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.54  thf('6', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.37/0.54  thf('7', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.37/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.54  thf('8', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.54      inference('sup+', [status(thm)], ['6', '7'])).
% 0.37/0.54  thf('9', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | ~ (v1_funct_1 @ X0)
% 0.37/0.54          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.37/0.54      inference('demod', [status(thm)], ['2', '5', '8'])).
% 0.37/0.54  thf(l13_xboole_0, axiom,
% 0.37/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.54  thf(fc3_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      (![X1 : $i, X2 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X2)) | ~ (v1_xboole_0 @ X2))),
% 0.37/0.54      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.54  thf('13', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.54  thf(t152_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.37/0.54  thf('14', plain,
% 0.37/0.54      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.37/0.54      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.54  thf('16', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X2))),
% 0.37/0.54      inference('sup-', [status(thm)], ['10', '15'])).
% 0.37/0.54  thf('17', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('condensation', [status(thm)], ['16'])).
% 0.37/0.54  thf('18', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.37/0.54          | ~ (v1_funct_1 @ X0)
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['9', '17'])).
% 0.37/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.54  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.54  thf('20', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.37/0.54          | ~ (v1_funct_1 @ X0)
% 0.37/0.54          | ~ (v1_relat_1 @ X0))),
% 0.37/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.54  thf('21', plain,
% 0.37/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.54  thf(t174_funct_1, conjecture,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.54       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i]:
% 0.37/0.54        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.54          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.37/0.54  thf('22', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('23', plain,
% 0.37/0.54      (![X0 : $i]: (~ (v5_funct_1 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.54  thf('24', plain,
% 0.37/0.54      ((~ (v1_relat_1 @ sk_A)
% 0.37/0.54        | ~ (v1_funct_1 @ sk_A)
% 0.37/0.54        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['20', '23'])).
% 0.37/0.54  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('26', plain, ((v1_funct_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.54  thf('28', plain, ($false),
% 0.37/0.54      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
