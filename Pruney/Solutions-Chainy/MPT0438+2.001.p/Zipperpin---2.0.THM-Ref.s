%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XS8Ov5bIDn

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  386 ( 449 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X16 @ X17 ) @ ( sk_D_1 @ X16 @ X17 ) ) @ X17 )
      | ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X23 )
      | ( r2_hidden @ X21 @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X16 @ X17 ) @ ( sk_D_1 @ X16 @ X17 ) ) @ X17 )
      | ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X23 )
      | ( r2_hidden @ X22 @ ( k2_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

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

thf(zf_stmt_0,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X5 )
      | ~ ( r2_hidden @ X0 @ X5 )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ( X2
       != ( k4_tarski @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X3: $i,X5: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X0 @ X5 )
      | ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ X3 @ X5 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X1 @ X0 ) @ X3 @ ( k4_tarski @ X3 @ ( sk_D_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X3 @ X2 ) @ ( sk_C @ X1 @ X0 ) @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D_1 @ X3 @ X2 ) ) @ ( k2_relat_1 @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X10 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ X0 ) @ ( sk_D_1 @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X16 @ X17 ) @ ( sk_D_1 @ X16 @ X17 ) ) @ X16 )
      | ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t21_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_relat_1])).

thf('18',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['19','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XS8Ov5bIDn
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 96 iterations in 0.095s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.55  thf(d3_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.55           ( ![C:$i,D:$i]:
% 0.21/0.55             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.21/0.55               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         ((r2_hidden @ 
% 0.21/0.55           (k4_tarski @ (sk_C @ X16 @ X17) @ (sk_D_1 @ X16 @ X17)) @ X17)
% 0.21/0.55          | (r1_tarski @ X17 @ X16)
% 0.21/0.55          | ~ (v1_relat_1 @ X17))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.55  thf(t20_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ C ) =>
% 0.21/0.55       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.21/0.55         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.55           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.55         (~ (r2_hidden @ (k4_tarski @ X21 @ X22) @ X23)
% 0.21/0.55          | (r2_hidden @ X21 @ (k1_relat_1 @ X23))
% 0.21/0.55          | ~ (v1_relat_1 @ X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r1_tarski @ X0 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.55          | (r1_tarski @ X0 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         ((r2_hidden @ 
% 0.21/0.55           (k4_tarski @ (sk_C @ X16 @ X17) @ (sk_D_1 @ X16 @ X17)) @ X17)
% 0.21/0.55          | (r1_tarski @ X17 @ X16)
% 0.21/0.55          | ~ (v1_relat_1 @ X17))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.55         (~ (r2_hidden @ (k4_tarski @ X21 @ X22) @ X23)
% 0.21/0.55          | (r2_hidden @ X22 @ (k2_relat_1 @ X23))
% 0.21/0.55          | ~ (v1_relat_1 @ X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r1_tarski @ X0 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r2_hidden @ (sk_D_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_D_1 @ X1 @ X0) @ (k2_relat_1 @ X0))
% 0.21/0.55          | (r1_tarski @ X0 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.55  thf(d2_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.55       ( ![D:$i]:
% 0.21/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.55           ( ?[E:$i,F:$i]:
% 0.21/0.55             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.55               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, axiom,
% 0.21/0.55    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.21/0.55     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.21/0.55       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.55         ( r2_hidden @ E @ A ) ) ))).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.21/0.55         ((zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X5)
% 0.21/0.55          | ~ (r2_hidden @ X0 @ X5)
% 0.21/0.55          | ~ (r2_hidden @ X1 @ X3)
% 0.21/0.55          | ((X2) != (k4_tarski @ X0 @ X1)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X3 : $i, X5 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X1 @ X3)
% 0.21/0.55          | ~ (r2_hidden @ X0 @ X5)
% 0.21/0.55          | (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ X0 @ X1) @ X3 @ X5))),
% 0.21/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r1_tarski @ X0 @ X1)
% 0.21/0.55          | (zip_tseitin_0 @ (sk_D_1 @ X1 @ X0) @ X3 @ 
% 0.21/0.55             (k4_tarski @ X3 @ (sk_D_1 @ X1 @ X0)) @ (k2_relat_1 @ X0) @ X2)
% 0.21/0.55          | ~ (r2_hidden @ X3 @ X2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r1_tarski @ X0 @ X1)
% 0.21/0.55          | (zip_tseitin_0 @ (sk_D_1 @ X3 @ X2) @ (sk_C @ X1 @ X0) @ 
% 0.21/0.55             (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D_1 @ X3 @ X2)) @ 
% 0.21/0.55             (k2_relat_1 @ X2) @ (k1_relat_1 @ X0))
% 0.21/0.55          | (r1_tarski @ X2 @ X3)
% 0.21/0.55          | ~ (v1_relat_1 @ X2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '10'])).
% 0.21/0.55  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.21/0.55  thf(zf_stmt_2, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.55       ( ![D:$i]:
% 0.21/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.55           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.55         (~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.21/0.55          | (r2_hidden @ X8 @ X11)
% 0.21/0.55          | ((X11) != (k2_zfmisc_1 @ X10 @ X9)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.55         ((r2_hidden @ X8 @ (k2_zfmisc_1 @ X10 @ X9))
% 0.21/0.55          | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10))),
% 0.21/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X1)
% 0.21/0.55          | (r1_tarski @ X1 @ X2)
% 0.21/0.55          | (r1_tarski @ X0 @ X3)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ (sk_C @ X3 @ X0) @ (sk_D_1 @ X2 @ X1)) @ 
% 0.21/0.55             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['11', '13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         (~ (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ (sk_C @ X16 @ X17) @ (sk_D_1 @ X16 @ X17)) @ X16)
% 0.21/0.55          | (r1_tarski @ X17 @ X16)
% 0.21/0.55          | ~ (v1_relat_1 @ X17))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r1_tarski @ X0 @ 
% 0.21/0.55             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.21/0.55          | (r1_tarski @ X0 @ 
% 0.21/0.55             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r1_tarski @ X0 @ 
% 0.21/0.55             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_tarski @ X0 @ 
% 0.21/0.55           (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.55  thf(t21_relat_1, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( r1_tarski @
% 0.21/0.55         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_3, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( v1_relat_1 @ A ) =>
% 0.21/0.55          ( r1_tarski @
% 0.21/0.55            A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t21_relat_1])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (~ (r1_tarski @ sk_A @ 
% 0.21/0.55          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.55  thf('19', plain, (~ (v1_relat_1 @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.55  thf('20', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.55  thf('21', plain, ($false), inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
