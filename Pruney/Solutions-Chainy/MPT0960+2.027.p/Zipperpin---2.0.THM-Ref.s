%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HmVi4bGDf0

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   54 (  65 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  495 ( 597 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(t33_wellord2,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t33_wellord2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_wellord2 @ sk_A ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25
       != ( k1_wellord2 @ X24 ) )
      | ( ( k3_relat_1 @ X25 )
        = X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X24: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X24 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X24 ) )
        = X24 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X24: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X24 ) )
      = X24 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X16 @ X17 ) @ ( sk_D_1 @ X16 @ X17 ) ) @ X17 )
      | ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X23 )
      | ( r2_hidden @ X21 @ ( k3_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X24: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X24 ) )
      = X24 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X16 @ X17 ) @ ( sk_D_1 @ X16 @ X17 ) ) @ X17 )
      | ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('14',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X23 )
      | ( r2_hidden @ X22 @ ( k3_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X5 )
      | ~ ( r2_hidden @ X0 @ X5 )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ( X2
       != ( k4_tarski @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X3: $i,X5: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X0 @ X5 )
      | ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ X3 @ X5 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X3 @ ( k4_tarski @ X3 @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) ) @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X3 @ ( k1_wellord2 @ X2 ) ) @ ( sk_C @ X1 @ ( k1_wellord2 @ X0 ) ) @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X3 @ ( k1_wellord2 @ X2 ) ) ) @ X2 @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X2 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X10 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X1 ) @ X2 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k1_wellord2 @ X1 ) ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X16 @ X17 ) @ ( sk_D_1 @ X16 @ X17 ) ) @ X16 )
      | ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HmVi4bGDf0
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:10:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.54  % Solved by: fo/fo7.sh
% 0.19/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.54  % done 100 iterations in 0.117s
% 0.19/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.54  % SZS output start Refutation
% 0.19/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.19/0.54  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.19/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.54  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.19/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.54  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.19/0.54  thf(t33_wellord2, conjecture,
% 0.19/0.54    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.19/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.54    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(d1_wellord2, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ B ) =>
% 0.36/0.54       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.36/0.54         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.36/0.54           ( ![C:$i,D:$i]:
% 0.36/0.54             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.36/0.54               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.36/0.54                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X24 : $i, X25 : $i]:
% 0.36/0.54         (((X25) != (k1_wellord2 @ X24))
% 0.36/0.54          | ((k3_relat_1 @ X25) = (X24))
% 0.36/0.54          | ~ (v1_relat_1 @ X25))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X24 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ (k1_wellord2 @ X24))
% 0.36/0.54          | ((k3_relat_1 @ (k1_wellord2 @ X24)) = (X24)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['1'])).
% 0.36/0.54  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.36/0.54  thf('3', plain, (![X28 : $i]: (v1_relat_1 @ (k1_wellord2 @ X28))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.36/0.54  thf('4', plain, (![X24 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X24)) = (X24))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.54  thf(d3_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.54           ( ![C:$i,D:$i]:
% 0.36/0.54             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.36/0.54               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i]:
% 0.36/0.54         ((r2_hidden @ 
% 0.36/0.54           (k4_tarski @ (sk_C @ X16 @ X17) @ (sk_D_1 @ X16 @ X17)) @ X17)
% 0.36/0.54          | (r1_tarski @ X17 @ X16)
% 0.36/0.54          | ~ (v1_relat_1 @ X17))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.36/0.54  thf(t30_relat_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ C ) =>
% 0.36/0.54       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.36/0.54         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.36/0.54           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.54         (~ (r2_hidden @ (k4_tarski @ X21 @ X22) @ X23)
% 0.36/0.54          | (r2_hidden @ X21 @ (k3_relat_1 @ X23))
% 0.36/0.54          | ~ (v1_relat_1 @ X23))),
% 0.36/0.54      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X0)
% 0.36/0.54          | (r1_tarski @ X0 @ X1)
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_relat_1 @ X0))
% 0.36/0.54          | (r1_tarski @ X0 @ X1)
% 0.36/0.54          | ~ (v1_relat_1 @ X0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['7'])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_C @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.36/0.54          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.36/0.54      inference('sup+', [status(thm)], ['4', '8'])).
% 0.36/0.54  thf('10', plain, (![X28 : $i]: (v1_relat_1 @ (k1_wellord2 @ X28))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_C @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.36/0.54          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.36/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.54  thf('12', plain, (![X24 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X24)) = (X24))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i]:
% 0.36/0.54         ((r2_hidden @ 
% 0.36/0.54           (k4_tarski @ (sk_C @ X16 @ X17) @ (sk_D_1 @ X16 @ X17)) @ X17)
% 0.36/0.54          | (r1_tarski @ X17 @ X16)
% 0.36/0.54          | ~ (v1_relat_1 @ X17))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.54         (~ (r2_hidden @ (k4_tarski @ X21 @ X22) @ X23)
% 0.36/0.54          | (r2_hidden @ X22 @ (k3_relat_1 @ X23))
% 0.36/0.54          | ~ (v1_relat_1 @ X23))),
% 0.36/0.54      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X0)
% 0.36/0.54          | (r1_tarski @ X0 @ X1)
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | (r2_hidden @ (sk_D_1 @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_D_1 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 0.36/0.54          | (r1_tarski @ X0 @ X1)
% 0.36/0.54          | ~ (v1_relat_1 @ X0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['15'])).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.36/0.54          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.36/0.54      inference('sup+', [status(thm)], ['12', '16'])).
% 0.36/0.54  thf('18', plain, (![X28 : $i]: (v1_relat_1 @ (k1_wellord2 @ X28))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.36/0.54          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.36/0.54      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.54  thf(d2_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.36/0.54       ( ![D:$i]:
% 0.36/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.54           ( ?[E:$i,F:$i]:
% 0.36/0.54             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.36/0.54               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_1, axiom,
% 0.36/0.54    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.36/0.54     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.36/0.54       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.36/0.54         ( r2_hidden @ E @ A ) ) ))).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.36/0.54         ((zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X5)
% 0.36/0.54          | ~ (r2_hidden @ X0 @ X5)
% 0.36/0.54          | ~ (r2_hidden @ X1 @ X3)
% 0.36/0.54          | ((X2) != (k4_tarski @ X0 @ X1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X3 : $i, X5 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X1 @ X3)
% 0.36/0.54          | ~ (r2_hidden @ X0 @ X5)
% 0.36/0.54          | (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ X0 @ X1) @ X3 @ X5))),
% 0.36/0.54      inference('simplify', [status(thm)], ['20'])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((r1_tarski @ (k1_wellord2 @ X0) @ X1)
% 0.36/0.54          | (zip_tseitin_0 @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X3 @ 
% 0.36/0.54             (k4_tarski @ X3 @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0))) @ X0 @ X2)
% 0.36/0.54          | ~ (r2_hidden @ X3 @ X2))),
% 0.36/0.54      inference('sup-', [status(thm)], ['19', '21'])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((r1_tarski @ (k1_wellord2 @ X0) @ X1)
% 0.36/0.54          | (zip_tseitin_0 @ (sk_D_1 @ X3 @ (k1_wellord2 @ X2)) @ 
% 0.36/0.54             (sk_C @ X1 @ (k1_wellord2 @ X0)) @ 
% 0.36/0.54             (k4_tarski @ (sk_C @ X1 @ (k1_wellord2 @ X0)) @ 
% 0.36/0.54              (sk_D_1 @ X3 @ (k1_wellord2 @ X2))) @ 
% 0.36/0.54             X2 @ X0)
% 0.36/0.54          | (r1_tarski @ (k1_wellord2 @ X2) @ X3))),
% 0.36/0.54      inference('sup-', [status(thm)], ['11', '22'])).
% 0.36/0.54  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.36/0.54  thf(zf_stmt_3, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.36/0.54       ( ![D:$i]:
% 0.36/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.54           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.54         (~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.36/0.54          | (r2_hidden @ X8 @ X11)
% 0.36/0.54          | ((X11) != (k2_zfmisc_1 @ X10 @ X9)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.54         ((r2_hidden @ X8 @ (k2_zfmisc_1 @ X10 @ X9))
% 0.36/0.54          | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10))),
% 0.36/0.54      inference('simplify', [status(thm)], ['24'])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((r1_tarski @ (k1_wellord2 @ X1) @ X2)
% 0.36/0.54          | (r1_tarski @ (k1_wellord2 @ X0) @ X3)
% 0.36/0.54          | (r2_hidden @ 
% 0.36/0.54             (k4_tarski @ (sk_C @ X3 @ (k1_wellord2 @ X0)) @ 
% 0.36/0.54              (sk_D_1 @ X2 @ (k1_wellord2 @ X1))) @ 
% 0.36/0.54             (k2_zfmisc_1 @ X0 @ X1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['23', '25'])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i]:
% 0.36/0.54         (~ (r2_hidden @ 
% 0.36/0.54             (k4_tarski @ (sk_C @ X16 @ X17) @ (sk_D_1 @ X16 @ X17)) @ X16)
% 0.36/0.54          | (r1_tarski @ X17 @ X16)
% 0.36/0.54          | ~ (v1_relat_1 @ X17))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))
% 0.36/0.54          | (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))
% 0.36/0.54          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.36/0.54          | (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.54  thf('29', plain, (![X28 : $i]: (v1_relat_1 @ (k1_wellord2 @ X28))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))
% 0.36/0.54          | (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))
% 0.36/0.54          | (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0)))),
% 0.36/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['30'])).
% 0.36/0.54  thf('32', plain, ($false), inference('demod', [status(thm)], ['0', '31'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
