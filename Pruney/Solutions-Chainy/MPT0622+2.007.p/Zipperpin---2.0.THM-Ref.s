%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PlsWpdKIjD

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 170 expanded)
%              Number of leaves         :   25 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  642 (2464 expanded)
%              Number of equality atoms :   68 ( 330 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t17_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( ( ( k1_relat_1 @ B )
                = ( k1_relat_1 @ C ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_tarski @ A ) )
              & ( ( k2_relat_1 @ C )
                = ( k1_tarski @ A ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( ( ( k1_relat_1 @ B )
                  = ( k1_relat_1 @ C ) )
                & ( ( k2_relat_1 @ B )
                  = ( k1_tarski @ A ) )
                & ( ( k2_relat_1 @ C )
                  = ( k1_tarski @ A ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ( X32 = X31 )
      | ( r2_hidden @ ( sk_C @ X31 @ X32 ) @ ( k1_relat_1 @ X32 ) )
      | ( ( k1_relat_1 @ X32 )
       != ( k1_relat_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_B )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_B )
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_C_1 = sk_B )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_C_1 = sk_B )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X30 @ X29 ) @ ( k2_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16','17','20'])).

thf('22',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_B @ sk_C_1 ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 )
      | ( X16 = X17 )
      | ( X16 = X18 )
      | ( X16 = X19 )
      | ( X16 = X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ~ ( zip_tseitin_0 @ X27 @ X22 @ X23 @ X24 @ X25 )
      | ( X26
       != ( k2_enumset1 @ X25 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X22 @ X23 @ X24 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k2_enumset1 @ X25 @ X24 @ X23 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( X0 = sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_B @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['22','35'])).

thf('37',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ( X32 = X31 )
      | ( ( k1_funct_1 @ X32 @ ( sk_C @ X31 @ X32 ) )
       != ( k1_funct_1 @ X31 @ ( sk_C @ X31 @ X32 ) ) )
      | ( ( k1_relat_1 @ X32 )
       != ( k1_relat_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('38',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_B ) )
    | ( sk_C_1 = sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('40',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X30 @ X29 ) @ ( k2_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_C_1 ) ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_C_1 ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('46',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ( sk_C_1 = sk_B ) ),
    inference(demod,[status(thm)],['38','46','47','48','49','50','51'])).

thf('53',plain,(
    sk_C_1 = sk_B ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PlsWpdKIjD
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 46 iterations in 0.024s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.47  thf(t17_funct_1, conjecture,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.47       ( ![C:$i]:
% 0.19/0.47         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.47           ( ( ( ( k1_relat_1 @ B ) = ( k1_relat_1 @ C ) ) & 
% 0.19/0.47               ( ( k2_relat_1 @ B ) = ( k1_tarski @ A ) ) & 
% 0.19/0.47               ( ( k2_relat_1 @ C ) = ( k1_tarski @ A ) ) ) =>
% 0.19/0.47             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i]:
% 0.19/0.47        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.47          ( ![C:$i]:
% 0.19/0.47            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.47              ( ( ( ( k1_relat_1 @ B ) = ( k1_relat_1 @ C ) ) & 
% 0.19/0.47                  ( ( k2_relat_1 @ B ) = ( k1_tarski @ A ) ) & 
% 0.19/0.47                  ( ( k2_relat_1 @ C ) = ( k1_tarski @ A ) ) ) =>
% 0.19/0.47                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t17_funct_1])).
% 0.19/0.47  thf('0', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_1))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t9_funct_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.47           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.19/0.47               ( ![C:$i]:
% 0.19/0.47                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.19/0.47                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.19/0.47             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X31 : $i, X32 : $i]:
% 0.19/0.47         (~ (v1_relat_1 @ X31)
% 0.19/0.47          | ~ (v1_funct_1 @ X31)
% 0.19/0.47          | ((X32) = (X31))
% 0.19/0.47          | (r2_hidden @ (sk_C @ X31 @ X32) @ (k1_relat_1 @ X32))
% 0.19/0.47          | ((k1_relat_1 @ X32) != (k1_relat_1 @ X31))
% 0.19/0.47          | ~ (v1_funct_1 @ X32)
% 0.19/0.47          | ~ (v1_relat_1 @ X32))),
% 0.19/0.47      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((k1_relat_1 @ sk_B) != (k1_relat_1 @ X0))
% 0.19/0.47          | ~ (v1_relat_1 @ sk_C_1)
% 0.19/0.47          | ~ (v1_funct_1 @ sk_C_1)
% 0.19/0.47          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 0.19/0.47          | ((sk_C_1) = (X0))
% 0.19/0.47          | ~ (v1_funct_1 @ X0)
% 0.19/0.47          | ~ (v1_relat_1 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.47  thf('3', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('4', plain, ((v1_funct_1 @ sk_C_1)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('5', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_1))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((k1_relat_1 @ sk_B) != (k1_relat_1 @ X0))
% 0.19/0.47          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.19/0.47          | ((sk_C_1) = (X0))
% 0.19/0.47          | ~ (v1_funct_1 @ X0)
% 0.19/0.47          | ~ (v1_relat_1 @ X0))),
% 0.19/0.47      inference('demod', [status(thm)], ['2', '3', '4', '5'])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      ((~ (v1_relat_1 @ sk_B)
% 0.19/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.19/0.47        | ((sk_C_1) = (sk_B))
% 0.19/0.47        | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.19/0.47      inference('eq_res', [status(thm)], ['6'])).
% 0.19/0.47  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('9', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      ((((sk_C_1) = (sk_B))
% 0.19/0.48        | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.19/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.19/0.48  thf('11', plain, (((sk_B) != (sk_C_1))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k1_relat_1 @ sk_B))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf('13', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_1))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t12_funct_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.48       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.48         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X29 : $i, X30 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X29 @ (k1_relat_1 @ X30))
% 0.19/0.48          | (r2_hidden @ (k1_funct_1 @ X30 @ X29) @ (k2_relat_1 @ X30))
% 0.19/0.48          | ~ (v1_funct_1 @ X30)
% 0.19/0.48          | ~ (v1_relat_1 @ X30))),
% 0.19/0.48      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.19/0.48          | ~ (v1_relat_1 @ sk_C_1)
% 0.19/0.48          | ~ (v1_funct_1 @ sk_C_1)
% 0.19/0.48          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('17', plain, ((v1_funct_1 @ sk_C_1)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('18', plain, (((k2_relat_1 @ sk_C_1) = (k1_tarski @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('19', plain, (((k2_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('20', plain, (((k2_relat_1 @ sk_B) = (k2_relat_1 @ sk_C_1))),
% 0.19/0.48      inference('sup+', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.19/0.48          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.19/0.48      inference('demod', [status(thm)], ['15', '16', '17', '20'])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_B @ sk_C_1)) @ 
% 0.19/0.48        (k2_relat_1 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['12', '21'])).
% 0.19/0.48  thf(d2_enumset1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.48     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.19/0.48       ( ![F:$i]:
% 0.19/0.48         ( ( r2_hidden @ F @ E ) <=>
% 0.19/0.48           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.19/0.48                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_1, axiom,
% 0.19/0.48    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.19/0.48     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.19/0.48       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.19/0.48         ( ( F ) != ( D ) ) ) ))).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.48         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.19/0.48          | ((X16) = (X17))
% 0.19/0.48          | ((X16) = (X18))
% 0.19/0.48          | ((X16) = (X19))
% 0.19/0.48          | ((X16) = (X20)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.48  thf('24', plain, (((k2_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t69_enumset1, axiom,
% 0.19/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.48  thf('25', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.48  thf(t70_enumset1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]:
% 0.19/0.48         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.48  thf(t71_enumset1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.48         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.19/0.48      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.19/0.48  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.19/0.48  thf(zf_stmt_3, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.48     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.19/0.48       ( ![F:$i]:
% 0.19/0.48         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X27 @ X26)
% 0.19/0.48          | ~ (zip_tseitin_0 @ X27 @ X22 @ X23 @ X24 @ X25)
% 0.19/0.48          | ((X26) != (k2_enumset1 @ X25 @ X24 @ X23 @ X22)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X27 : $i]:
% 0.19/0.48         (~ (zip_tseitin_0 @ X27 @ X22 @ X23 @ X24 @ X25)
% 0.19/0.48          | ~ (r2_hidden @ X27 @ (k2_enumset1 @ X25 @ X24 @ X23 @ X22)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['28'])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.19/0.48          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.19/0.48      inference('sup-', [status(thm)], ['27', '29'])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.19/0.48          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['26', '30'])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.19/0.48          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['25', '31'])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.19/0.48          | ~ (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['24', '32'])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((X0) = (sk_A))
% 0.19/0.48          | ((X0) = (sk_A))
% 0.19/0.48          | ((X0) = (sk_A))
% 0.19/0.48          | ((X0) = (sk_A))
% 0.19/0.48          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['23', '33'])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['34'])).
% 0.19/0.48  thf('36', plain, (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_B @ sk_C_1)) = (sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['22', '35'])).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      (![X31 : $i, X32 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X31)
% 0.19/0.48          | ~ (v1_funct_1 @ X31)
% 0.19/0.48          | ((X32) = (X31))
% 0.19/0.48          | ((k1_funct_1 @ X32 @ (sk_C @ X31 @ X32))
% 0.19/0.48              != (k1_funct_1 @ X31 @ (sk_C @ X31 @ X32)))
% 0.19/0.48          | ((k1_relat_1 @ X32) != (k1_relat_1 @ X31))
% 0.19/0.48          | ~ (v1_funct_1 @ X32)
% 0.19/0.48          | ~ (v1_relat_1 @ X32))),
% 0.19/0.48      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_C_1)))
% 0.19/0.48        | ~ (v1_relat_1 @ sk_C_1)
% 0.19/0.48        | ~ (v1_funct_1 @ sk_C_1)
% 0.19/0.48        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_B))
% 0.19/0.48        | ((sk_C_1) = (sk_B))
% 0.19/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.19/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k1_relat_1 @ sk_B))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf('40', plain,
% 0.19/0.48      (![X29 : $i, X30 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X29 @ (k1_relat_1 @ X30))
% 0.19/0.48          | (r2_hidden @ (k1_funct_1 @ X30 @ X29) @ (k2_relat_1 @ X30))
% 0.19/0.48          | ~ (v1_funct_1 @ X30)
% 0.19/0.48          | ~ (v1_relat_1 @ X30))),
% 0.19/0.48      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      ((~ (v1_relat_1 @ sk_B)
% 0.19/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.19/0.48        | (r2_hidden @ (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_C_1)) @ 
% 0.19/0.48           (k2_relat_1 @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.48  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('44', plain,
% 0.19/0.48      ((r2_hidden @ (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_C_1)) @ 
% 0.19/0.48        (k2_relat_1 @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.19/0.48  thf('45', plain,
% 0.19/0.48      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['34'])).
% 0.19/0.48  thf('46', plain, (((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_C_1)) = (sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.48  thf('47', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('48', plain, ((v1_funct_1 @ sk_C_1)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('49', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_1))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('50', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('52', plain,
% 0.19/0.48      ((((sk_A) != (sk_A))
% 0.19/0.48        | ((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.19/0.48        | ((sk_C_1) = (sk_B)))),
% 0.19/0.48      inference('demod', [status(thm)],
% 0.19/0.48                ['38', '46', '47', '48', '49', '50', '51'])).
% 0.19/0.48  thf('53', plain, (((sk_C_1) = (sk_B))),
% 0.19/0.48      inference('simplify', [status(thm)], ['52'])).
% 0.19/0.48  thf('54', plain, (((sk_B) != (sk_C_1))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('55', plain, ($false),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
