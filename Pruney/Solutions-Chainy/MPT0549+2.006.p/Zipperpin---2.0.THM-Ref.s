%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eicp5mVVCn

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 131 expanded)
%              Number of leaves         :   22 (  44 expanded)
%              Depth                    :   19
%              Number of atoms          :  475 (1068 expanded)
%              Number of equality atoms :   39 (  96 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t151_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t151_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X48 ) @ X49 )
      | ( ( k7_relat_1 @ X48 @ X49 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('6',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X45 @ X46 ) )
        = ( k9_relat_1 @ X45 @ X46 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('10',plain,
    ( ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_xboole_0
      = ( k9_relat_1 @ sk_B @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k9_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','16'])).

thf('18',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','17'])).

thf('19',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('20',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('21',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','16','20'])).

thf('22',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X45 @ X46 ) )
        = ( k9_relat_1 @ X45 @ X46 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X47: $i] :
      ( ( r1_tarski @ X47 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X47 ) @ ( k2_relat_1 @ X47 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ k1_xboole_0 ) @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ k1_xboole_0 )
      = ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('33',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('34',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X36 @ X37 ) )
      | ~ ( r1_xboole_0 @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('36',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('38',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('40',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['32','37','38','39'])).

thf('41',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k7_relat_1 @ X48 @ X49 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X48 ) @ X49 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['18','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eicp5mVVCn
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:26:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 77 iterations in 0.043s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(t151_relat_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( v1_relat_1 @ B ) =>
% 0.20/0.50          ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t151_relat_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.20/0.50        | ((k9_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.20/0.50         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.20/0.50       ~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.20/0.50        | ((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.20/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf(t95_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X48 : $i, X49 : $i]:
% 0.20/0.50         (~ (r1_xboole_0 @ (k1_relat_1 @ X48) @ X49)
% 0.20/0.50          | ((k7_relat_1 @ X48 @ X49) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ X48))),
% 0.20/0.50      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (((~ (v1_relat_1 @ sk_B) | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.20/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.20/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf(t148_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X45 : $i, X46 : $i]:
% 0.20/0.50         (((k2_relat_1 @ (k7_relat_1 @ X45 @ X46)) = (k9_relat_1 @ X45 @ X46))
% 0.20/0.50          | ~ (v1_relat_1 @ X45))),
% 0.20/0.50      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (((((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ sk_B @ sk_A))
% 0.20/0.50         | ~ (v1_relat_1 @ sk_B)))
% 0.20/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf(t60_relat_1, axiom,
% 0.20/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('11', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.50  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      ((((k1_xboole_0) = (k9_relat_1 @ sk_B @ sk_A)))
% 0.20/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      ((((k9_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.20/0.50         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.50         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.20/0.50             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.50       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.50  thf('17', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['2', '16'])).
% 0.20/0.50  thf('18', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['1', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.20/0.50         <= ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.50       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('21', plain, ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['2', '16', '20'])).
% 0.20/0.50  thf('22', plain, (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['19', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X45 : $i, X46 : $i]:
% 0.20/0.50         (((k2_relat_1 @ (k7_relat_1 @ X45 @ X46)) = (k9_relat_1 @ X45 @ X46))
% 0.20/0.50          | ~ (v1_relat_1 @ X45))),
% 0.20/0.50      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.50  thf(t21_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( r1_tarski @
% 0.20/0.50         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X47 : $i]:
% 0.20/0.50         ((r1_tarski @ X47 @ 
% 0.20/0.50           (k2_zfmisc_1 @ (k1_relat_1 @ X47) @ (k2_relat_1 @ X47)))
% 0.20/0.50          | ~ (v1_relat_1 @ X47))),
% 0.20/0.50      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 0.20/0.50           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.20/0.50            (k9_relat_1 @ X1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf(dt_k7_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X43 : $i, X44 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X43) | (v1_relat_1 @ (k7_relat_1 @ X43 @ X44)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X1)
% 0.20/0.50          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 0.20/0.50             (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.20/0.50              (k9_relat_1 @ X1 @ X0))))),
% 0.20/0.50      inference('clc', [status(thm)], ['25', '26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (((r1_tarski @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.20/0.50         (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ k1_xboole_0))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.50      inference('sup+', [status(thm)], ['22', '27'])).
% 0.20/0.50  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      ((r1_tarski @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.20/0.50        (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i, X2 : $i]:
% 0.20/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((~ (r1_tarski @ 
% 0.20/0.50           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ 
% 0.20/0.50            k1_xboole_0) @ 
% 0.20/0.50           (k7_relat_1 @ sk_B @ sk_A))
% 0.20/0.50        | ((k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ 
% 0.20/0.50            k1_xboole_0) = (k7_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.50  thf('33', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.50  thf(t127_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.20/0.50       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ (k2_zfmisc_1 @ X34 @ X35) @ (k2_zfmisc_1 @ X36 @ X37))
% 0.20/0.50          | ~ (r1_xboole_0 @ X35 @ X37))),
% 0.20/0.50      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ 
% 0.20/0.50          (k2_zfmisc_1 @ X1 @ k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf(t66_xboole_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.20/0.50       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.50  thf('38', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('40', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '37', '38', '39'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X48 : $i, X49 : $i]:
% 0.20/0.50         (((k7_relat_1 @ X48 @ X49) != (k1_xboole_0))
% 0.20/0.50          | (r1_xboole_0 @ (k1_relat_1 @ X48) @ X49)
% 0.20/0.50          | ~ (v1_relat_1 @ X48))),
% 0.20/0.50      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.50        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.50  thf('45', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.20/0.50      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.50  thf('46', plain, ($false), inference('demod', [status(thm)], ['18', '45'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
