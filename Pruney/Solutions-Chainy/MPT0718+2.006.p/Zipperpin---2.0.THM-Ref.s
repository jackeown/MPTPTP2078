%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kJo9JlqBO5

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:24 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 (  75 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  293 ( 703 expanded)
%              Number of equality atoms :    6 (  28 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_relat_1_type,type,(
    v2_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t173_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v5_funct_1 @ A @ B )
              & ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) ) )
           => ( v2_relat_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v5_funct_1 @ A @ B )
                & ( ( k1_relat_1 @ A )
                  = ( k1_relat_1 @ B ) ) )
             => ( v2_relat_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t173_funct_1])).

thf('0',plain,(
    ~ ( v2_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d15_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_relat_1 @ A )
      <=> ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( v1_xboole_0 @ ( k1_funct_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ ( k1_funct_1 @ X4 @ ( sk_B @ X4 ) ) )
      | ( v2_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d15_funct_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_relat_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v5_funct_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ ( sk_B @ X4 ) @ ( k1_relat_1 @ X4 ) )
      | ( v2_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d15_funct_1])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) )
    | ( v2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ~ ( v2_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

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

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v5_funct_1 @ X6 @ X7 )
      | ( r2_hidden @ ( k1_funct_1 @ X6 @ X8 ) @ ( k1_funct_1 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( v5_funct_1 @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( v5_funct_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( v2_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['3','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( v2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('26',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_relat_1 @ sk_B_1 ),
    inference(clc,[status(thm)],['25','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kJo9JlqBO5
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:23:36 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.19/0.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.43  % Solved by: fo/fo7.sh
% 0.19/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.43  % done 28 iterations in 0.018s
% 0.19/0.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.43  % SZS output start Refutation
% 0.19/0.43  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.43  thf(v2_relat_1_type, type, v2_relat_1: $i > $o).
% 0.19/0.43  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.43  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.43  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.43  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.19/0.43  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.43  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.43  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.43  thf(t173_funct_1, conjecture,
% 0.19/0.43    (![A:$i]:
% 0.19/0.43     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.43       ( ![B:$i]:
% 0.19/0.43         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.43           ( ( ( v5_funct_1 @ A @ B ) & 
% 0.19/0.43               ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) ) =>
% 0.19/0.43             ( v2_relat_1 @ B ) ) ) ) ))).
% 0.19/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.43    (~( ![A:$i]:
% 0.19/0.43        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.43          ( ![B:$i]:
% 0.19/0.43            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.43              ( ( ( v5_funct_1 @ A @ B ) & 
% 0.19/0.43                  ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) ) =>
% 0.19/0.43                ( v2_relat_1 @ B ) ) ) ) ) )),
% 0.19/0.43    inference('cnf.neg', [status(esa)], [t173_funct_1])).
% 0.19/0.43  thf('0', plain, (~ (v2_relat_1 @ sk_B_1)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf(d15_funct_1, axiom,
% 0.19/0.43    (![A:$i]:
% 0.19/0.43     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.43       ( ( v2_relat_1 @ A ) <=>
% 0.19/0.43         ( ![B:$i]:
% 0.19/0.43           ( ~( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.19/0.43                ( v1_xboole_0 @ ( k1_funct_1 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.43  thf('1', plain,
% 0.19/0.43      (![X4 : $i]:
% 0.19/0.43         ((v1_xboole_0 @ (k1_funct_1 @ X4 @ (sk_B @ X4)))
% 0.19/0.43          | (v2_relat_1 @ X4)
% 0.19/0.43          | ~ (v1_funct_1 @ X4)
% 0.19/0.43          | ~ (v1_relat_1 @ X4))),
% 0.19/0.43      inference('cnf', [status(esa)], [d15_funct_1])).
% 0.19/0.43  thf(l13_xboole_0, axiom,
% 0.19/0.43    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.43  thf('2', plain,
% 0.19/0.43      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.43      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.43  thf('3', plain,
% 0.19/0.43      (![X0 : $i]:
% 0.19/0.43         (~ (v1_relat_1 @ X0)
% 0.19/0.43          | ~ (v1_funct_1 @ X0)
% 0.19/0.43          | (v2_relat_1 @ X0)
% 0.19/0.43          | ((k1_funct_1 @ X0 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.19/0.43      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.43  thf('4', plain, ((v5_funct_1 @ sk_A @ sk_B_1)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('5', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('6', plain,
% 0.19/0.43      (![X4 : $i]:
% 0.19/0.43         ((r2_hidden @ (sk_B @ X4) @ (k1_relat_1 @ X4))
% 0.19/0.43          | (v2_relat_1 @ X4)
% 0.19/0.43          | ~ (v1_funct_1 @ X4)
% 0.19/0.43          | ~ (v1_relat_1 @ X4))),
% 0.19/0.43      inference('cnf', [status(esa)], [d15_funct_1])).
% 0.19/0.43  thf('7', plain,
% 0.19/0.43      (((r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_A))
% 0.19/0.43        | ~ (v1_relat_1 @ sk_B_1)
% 0.19/0.43        | ~ (v1_funct_1 @ sk_B_1)
% 0.19/0.43        | (v2_relat_1 @ sk_B_1))),
% 0.19/0.43      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.43  thf('8', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('9', plain, ((v1_funct_1 @ sk_B_1)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('10', plain,
% 0.19/0.43      (((r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_A))
% 0.19/0.43        | (v2_relat_1 @ sk_B_1))),
% 0.19/0.43      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.19/0.43  thf('11', plain, (~ (v2_relat_1 @ sk_B_1)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('12', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_A))),
% 0.19/0.43      inference('clc', [status(thm)], ['10', '11'])).
% 0.19/0.43  thf(d20_funct_1, axiom,
% 0.19/0.43    (![A:$i]:
% 0.19/0.43     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.43       ( ![B:$i]:
% 0.19/0.43         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.43           ( ( v5_funct_1 @ B @ A ) <=>
% 0.19/0.43             ( ![C:$i]:
% 0.19/0.43               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.43                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.19/0.43  thf('13', plain,
% 0.19/0.43      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.43         (~ (v1_relat_1 @ X6)
% 0.19/0.43          | ~ (v1_funct_1 @ X6)
% 0.19/0.43          | ~ (v5_funct_1 @ X6 @ X7)
% 0.19/0.43          | (r2_hidden @ (k1_funct_1 @ X6 @ X8) @ (k1_funct_1 @ X7 @ X8))
% 0.19/0.43          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X6))
% 0.19/0.43          | ~ (v1_funct_1 @ X7)
% 0.19/0.43          | ~ (v1_relat_1 @ X7))),
% 0.19/0.43      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.19/0.43  thf('14', plain,
% 0.19/0.43      (![X0 : $i]:
% 0.19/0.43         (~ (v1_relat_1 @ X0)
% 0.19/0.43          | ~ (v1_funct_1 @ X0)
% 0.19/0.43          | (r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 0.19/0.43             (k1_funct_1 @ X0 @ (sk_B @ sk_B_1)))
% 0.19/0.43          | ~ (v5_funct_1 @ sk_A @ X0)
% 0.19/0.43          | ~ (v1_funct_1 @ sk_A)
% 0.19/0.43          | ~ (v1_relat_1 @ sk_A))),
% 0.19/0.43      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.43  thf('15', plain, ((v1_funct_1 @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('17', plain,
% 0.19/0.43      (![X0 : $i]:
% 0.19/0.43         (~ (v1_relat_1 @ X0)
% 0.19/0.43          | ~ (v1_funct_1 @ X0)
% 0.19/0.43          | (r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 0.19/0.43             (k1_funct_1 @ X0 @ (sk_B @ sk_B_1)))
% 0.19/0.43          | ~ (v5_funct_1 @ sk_A @ X0))),
% 0.19/0.43      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.19/0.43  thf('18', plain,
% 0.19/0.43      (((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 0.19/0.43         (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.19/0.43        | ~ (v1_funct_1 @ sk_B_1)
% 0.19/0.43        | ~ (v1_relat_1 @ sk_B_1))),
% 0.19/0.43      inference('sup-', [status(thm)], ['4', '17'])).
% 0.19/0.43  thf('19', plain, ((v1_funct_1 @ sk_B_1)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('20', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('21', plain,
% 0.19/0.43      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 0.19/0.43        (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 0.19/0.43      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.19/0.43  thf('22', plain,
% 0.19/0.43      (((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ k1_xboole_0)
% 0.19/0.43        | (v2_relat_1 @ sk_B_1)
% 0.19/0.43        | ~ (v1_funct_1 @ sk_B_1)
% 0.19/0.43        | ~ (v1_relat_1 @ sk_B_1))),
% 0.19/0.43      inference('sup+', [status(thm)], ['3', '21'])).
% 0.19/0.43  thf('23', plain, ((v1_funct_1 @ sk_B_1)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('24', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('25', plain,
% 0.19/0.43      (((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ k1_xboole_0)
% 0.19/0.43        | (v2_relat_1 @ sk_B_1))),
% 0.19/0.43      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.19/0.43  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.19/0.43  thf('26', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.19/0.43      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.19/0.43  thf(l24_zfmisc_1, axiom,
% 0.19/0.43    (![A:$i,B:$i]:
% 0.19/0.43     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.43  thf('27', plain,
% 0.19/0.43      (![X2 : $i, X3 : $i]:
% 0.19/0.43         (~ (r1_xboole_0 @ (k1_tarski @ X2) @ X3) | ~ (r2_hidden @ X2 @ X3))),
% 0.19/0.43      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.19/0.43  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.43      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.43  thf('29', plain, ((v2_relat_1 @ sk_B_1)),
% 0.19/0.43      inference('clc', [status(thm)], ['25', '28'])).
% 0.19/0.43  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 0.19/0.43  
% 0.19/0.43  % SZS output end Refutation
% 0.19/0.43  
% 0.19/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
