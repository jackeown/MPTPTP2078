%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KSTuSpPiGM

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:25 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   52 (  75 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  291 ( 701 expanded)
%              Number of equality atoms :   11 (  33 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_relat_1_type,type,(
    v2_relat_1: $i > $o )).

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
    ! [X6: $i] :
      ( ( v1_xboole_0 @ ( k1_funct_1 @ X6 @ ( sk_B @ X6 ) ) )
      | ( v2_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d15_funct_1])).

thf('2',plain,(
    v5_funct_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X6: $i] :
      ( ( r2_hidden @ ( sk_B @ X6 ) @ ( k1_relat_1 @ X6 ) )
      | ( v2_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d15_funct_1])).

thf('5',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) )
    | ( v2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ~ ( v2_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v5_funct_1 @ X8 @ X9 )
      | ( r2_hidden @ ( k1_funct_1 @ X8 @ X10 ) @ ( k1_funct_1 @ X9 @ X10 ) )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( v5_funct_1 @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( v5_funct_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('22',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KSTuSpPiGM
% 0.14/0.36  % Computer   : n001.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 13:56:00 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.52  % Solved by: fo/fo7.sh
% 0.23/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.52  % done 60 iterations in 0.040s
% 0.23/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.52  % SZS output start Refutation
% 0.23/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.52  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.23/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.52  thf(v2_relat_1_type, type, v2_relat_1: $i > $o).
% 0.23/0.52  thf(t173_funct_1, conjecture,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.52           ( ( ( v5_funct_1 @ A @ B ) & 
% 0.23/0.52               ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) ) =>
% 0.23/0.52             ( v2_relat_1 @ B ) ) ) ) ))).
% 0.23/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.52    (~( ![A:$i]:
% 0.23/0.52        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.52          ( ![B:$i]:
% 0.23/0.52            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.52              ( ( ( v5_funct_1 @ A @ B ) & 
% 0.23/0.52                  ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) ) =>
% 0.23/0.52                ( v2_relat_1 @ B ) ) ) ) ) )),
% 0.23/0.52    inference('cnf.neg', [status(esa)], [t173_funct_1])).
% 0.23/0.52  thf('0', plain, (~ (v2_relat_1 @ sk_B_1)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(d15_funct_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.52       ( ( v2_relat_1 @ A ) <=>
% 0.23/0.52         ( ![B:$i]:
% 0.23/0.52           ( ~( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.23/0.52                ( v1_xboole_0 @ ( k1_funct_1 @ A @ B ) ) ) ) ) ) ))).
% 0.23/0.52  thf('1', plain,
% 0.23/0.52      (![X6 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ (k1_funct_1 @ X6 @ (sk_B @ X6)))
% 0.23/0.52          | (v2_relat_1 @ X6)
% 0.23/0.52          | ~ (v1_funct_1 @ X6)
% 0.23/0.52          | ~ (v1_relat_1 @ X6))),
% 0.23/0.52      inference('cnf', [status(esa)], [d15_funct_1])).
% 0.23/0.52  thf('2', plain, ((v5_funct_1 @ sk_A @ sk_B_1)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('3', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('4', plain,
% 0.23/0.52      (![X6 : $i]:
% 0.23/0.52         ((r2_hidden @ (sk_B @ X6) @ (k1_relat_1 @ X6))
% 0.23/0.52          | (v2_relat_1 @ X6)
% 0.23/0.52          | ~ (v1_funct_1 @ X6)
% 0.23/0.52          | ~ (v1_relat_1 @ X6))),
% 0.23/0.52      inference('cnf', [status(esa)], [d15_funct_1])).
% 0.23/0.52  thf('5', plain,
% 0.23/0.52      (((r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_A))
% 0.23/0.52        | ~ (v1_relat_1 @ sk_B_1)
% 0.23/0.52        | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.52        | (v2_relat_1 @ sk_B_1))),
% 0.23/0.52      inference('sup+', [status(thm)], ['3', '4'])).
% 0.23/0.52  thf('6', plain, ((v1_relat_1 @ sk_B_1)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('7', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('8', plain,
% 0.23/0.52      (((r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_A))
% 0.23/0.52        | (v2_relat_1 @ sk_B_1))),
% 0.23/0.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.23/0.52  thf('9', plain, (~ (v2_relat_1 @ sk_B_1)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('10', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_A))),
% 0.23/0.52      inference('clc', [status(thm)], ['8', '9'])).
% 0.23/0.52  thf(d20_funct_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.52           ( ( v5_funct_1 @ B @ A ) <=>
% 0.23/0.52             ( ![C:$i]:
% 0.23/0.52               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.23/0.52                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.23/0.52  thf('11', plain,
% 0.23/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.52         (~ (v1_relat_1 @ X8)
% 0.23/0.52          | ~ (v1_funct_1 @ X8)
% 0.23/0.52          | ~ (v5_funct_1 @ X8 @ X9)
% 0.23/0.52          | (r2_hidden @ (k1_funct_1 @ X8 @ X10) @ (k1_funct_1 @ X9 @ X10))
% 0.23/0.52          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X8))
% 0.23/0.52          | ~ (v1_funct_1 @ X9)
% 0.23/0.52          | ~ (v1_relat_1 @ X9))),
% 0.23/0.52      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.23/0.52  thf('12', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (v1_relat_1 @ X0)
% 0.23/0.52          | ~ (v1_funct_1 @ X0)
% 0.23/0.52          | (r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 0.23/0.52             (k1_funct_1 @ X0 @ (sk_B @ sk_B_1)))
% 0.23/0.52          | ~ (v5_funct_1 @ sk_A @ X0)
% 0.23/0.52          | ~ (v1_funct_1 @ sk_A)
% 0.23/0.52          | ~ (v1_relat_1 @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.52  thf('13', plain, ((v1_funct_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('15', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (v1_relat_1 @ X0)
% 0.23/0.52          | ~ (v1_funct_1 @ X0)
% 0.23/0.52          | (r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 0.23/0.52             (k1_funct_1 @ X0 @ (sk_B @ sk_B_1)))
% 0.23/0.52          | ~ (v5_funct_1 @ sk_A @ X0))),
% 0.23/0.52      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.23/0.52  thf('16', plain,
% 0.23/0.52      (((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 0.23/0.52         (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.23/0.52        | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.52        | ~ (v1_relat_1 @ sk_B_1))),
% 0.23/0.52      inference('sup-', [status(thm)], ['2', '15'])).
% 0.23/0.52  thf('17', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('18', plain, ((v1_relat_1 @ sk_B_1)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('19', plain,
% 0.23/0.52      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 0.23/0.52        (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 0.23/0.52      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.23/0.52  thf(l13_xboole_0, axiom,
% 0.23/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.52  thf('20', plain,
% 0.23/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.23/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.23/0.52  thf(t113_zfmisc_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.23/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.52  thf('21', plain,
% 0.23/0.52      (![X2 : $i, X3 : $i]:
% 0.23/0.52         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.23/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.23/0.52  thf('22', plain,
% 0.23/0.52      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.23/0.52  thf(t152_zfmisc_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.23/0.52  thf('23', plain,
% 0.23/0.52      (![X4 : $i, X5 : $i]: ~ (r2_hidden @ X4 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.23/0.52      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.23/0.52  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.23/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.52  thf('25', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['20', '24'])).
% 0.23/0.52  thf('26', plain, (~ (v1_xboole_0 @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['19', '25'])).
% 0.23/0.52  thf('27', plain,
% 0.23/0.52      ((~ (v1_relat_1 @ sk_B_1)
% 0.23/0.52        | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.52        | (v2_relat_1 @ sk_B_1))),
% 0.23/0.52      inference('sup-', [status(thm)], ['1', '26'])).
% 0.23/0.52  thf('28', plain, ((v1_relat_1 @ sk_B_1)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('29', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('30', plain, ((v2_relat_1 @ sk_B_1)),
% 0.23/0.52      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.23/0.52  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.23/0.52  
% 0.23/0.52  % SZS output end Refutation
% 0.23/0.52  
% 0.23/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
