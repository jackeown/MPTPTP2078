%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZAgkuoXzMR

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 163 expanded)
%              Number of leaves         :   23 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  586 (2356 expanded)
%              Number of equality atoms :   62 ( 319 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( X25 = X24 )
      | ( r2_hidden @ ( sk_C @ X24 @ X25 ) @ ( k1_relat_1 @ X25 ) )
      | ( ( k1_relat_1 @ X25 )
       != ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X23 @ X22 ) @ ( k2_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
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
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( X0 = sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_B @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( X25 = X24 )
      | ( ( k1_funct_1 @ X25 @ ( sk_C @ X24 @ X25 ) )
       != ( k1_funct_1 @ X24 @ ( sk_C @ X24 @ X25 ) ) )
      | ( ( k1_relat_1 @ X25 )
       != ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('36',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_B ) )
    | ( sk_C_1 = sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('38',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X23 @ X22 ) @ ( k2_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_C_1 ) ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_C_1 ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('44',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ( sk_C_1 = sk_B ) ),
    inference(demod,[status(thm)],['36','44','45','46','47','48','49'])).

thf('51',plain,(
    sk_C_1 = sk_B ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZAgkuoXzMR
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:20:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 76 iterations in 0.036s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(t17_funct_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49           ( ( ( ( k1_relat_1 @ B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.49               ( ( k2_relat_1 @ B ) = ( k1_tarski @ A ) ) & 
% 0.20/0.49               ( ( k2_relat_1 @ C ) = ( k1_tarski @ A ) ) ) =>
% 0.20/0.49             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49          ( ![C:$i]:
% 0.20/0.49            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49              ( ( ( ( k1_relat_1 @ B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.49                  ( ( k2_relat_1 @ B ) = ( k1_tarski @ A ) ) & 
% 0.20/0.49                  ( ( k2_relat_1 @ C ) = ( k1_tarski @ A ) ) ) =>
% 0.20/0.49                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t17_funct_1])).
% 0.20/0.49  thf('0', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t9_funct_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.20/0.49               ( ![C:$i]:
% 0.20/0.49                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.49                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.20/0.49             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X24 : $i, X25 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X24)
% 0.20/0.49          | ~ (v1_funct_1 @ X24)
% 0.20/0.49          | ((X25) = (X24))
% 0.20/0.49          | (r2_hidden @ (sk_C @ X24 @ X25) @ (k1_relat_1 @ X25))
% 0.20/0.49          | ((k1_relat_1 @ X25) != (k1_relat_1 @ X24))
% 0.20/0.49          | ~ (v1_funct_1 @ X25)
% 0.20/0.49          | ~ (v1_relat_1 @ X25))),
% 0.20/0.49      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_relat_1 @ sk_B) != (k1_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.49          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 0.20/0.49          | ((sk_C_1) = (X0))
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf('3', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('4', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('5', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_relat_1 @ sk_B) != (k1_relat_1 @ X0))
% 0.20/0.49          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.20/0.49          | ((sk_C_1) = (X0))
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['2', '3', '4', '5'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49        | ((sk_C_1) = (sk_B))
% 0.20/0.49        | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.20/0.49      inference('eq_res', [status(thm)], ['6'])).
% 0.20/0.49  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      ((((sk_C_1) = (sk_B))
% 0.20/0.49        | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.49  thf('11', plain, (((sk_B) != (sk_C_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k1_relat_1 @ sk_B))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t12_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.49         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X22 : $i, X23 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 0.20/0.49          | (r2_hidden @ (k1_funct_1 @ X23 @ X22) @ (k2_relat_1 @ X23))
% 0.20/0.49          | ~ (v1_funct_1 @ X23)
% 0.20/0.49          | ~ (v1_relat_1 @ X23))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.20/0.49          | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.49          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain, (((k2_relat_1 @ sk_C_1) = (k1_tarski @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain, (((k2_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('20', plain, (((k2_relat_1 @ sk_B) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.20/0.49          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16', '17', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_B @ sk_C_1)) @ 
% 0.20/0.49        (k2_relat_1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '21'])).
% 0.20/0.49  thf(d1_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.49       ( ![E:$i]:
% 0.20/0.49         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.49           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_1, axiom,
% 0.20/0.49    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.49       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.20/0.49          | ((X1) = (X2))
% 0.20/0.49          | ((X1) = (X3))
% 0.20/0.49          | ((X1) = (X4)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.49  thf('24', plain, (((k2_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t69_enumset1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf(t70_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i]:
% 0.20/0.49         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.49  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_3, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.49       ( ![E:$i]:
% 0.20/0.49         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.49          | ~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.20/0.49          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.20/0.49         (~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.20/0.49          | ~ (r2_hidden @ X10 @ (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.49          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.49          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.20/0.49          | ~ (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((X0) = (sk_A))
% 0.20/0.49          | ((X0) = (sk_A))
% 0.20/0.49          | ((X0) = (sk_A))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.49  thf('34', plain, (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_B @ sk_C_1)) = (sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X24 : $i, X25 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X24)
% 0.20/0.49          | ~ (v1_funct_1 @ X24)
% 0.20/0.49          | ((X25) = (X24))
% 0.20/0.49          | ((k1_funct_1 @ X25 @ (sk_C @ X24 @ X25))
% 0.20/0.49              != (k1_funct_1 @ X24 @ (sk_C @ X24 @ X25)))
% 0.20/0.49          | ((k1_relat_1 @ X25) != (k1_relat_1 @ X24))
% 0.20/0.49          | ~ (v1_funct_1 @ X25)
% 0.20/0.49          | ~ (v1_relat_1 @ X25))),
% 0.20/0.49      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_C_1)))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.49        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_B))
% 0.20/0.49        | ((sk_C_1) = (sk_B))
% 0.20/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k1_relat_1 @ sk_B))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X22 : $i, X23 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 0.20/0.49          | (r2_hidden @ (k1_funct_1 @ X23 @ X22) @ (k2_relat_1 @ X23))
% 0.20/0.49          | ~ (v1_funct_1 @ X23)
% 0.20/0.49          | ~ (v1_relat_1 @ X23))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49        | (r2_hidden @ (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_C_1)) @ 
% 0.20/0.49           (k2_relat_1 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('41', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      ((r2_hidden @ (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_C_1)) @ 
% 0.20/0.49        (k2_relat_1 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.49  thf('44', plain, (((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_C_1)) = (sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('45', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('46', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('47', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      ((((sk_A) != (sk_A))
% 0.20/0.49        | ((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.20/0.49        | ((sk_C_1) = (sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)],
% 0.20/0.49                ['36', '44', '45', '46', '47', '48', '49'])).
% 0.20/0.49  thf('51', plain, (((sk_C_1) = (sk_B))),
% 0.20/0.49      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.49  thf('52', plain, (((sk_B) != (sk_C_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('53', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
