%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bgPYCBJ2cQ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:43 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 278 expanded)
%              Number of leaves         :   21 (  79 expanded)
%              Depth                    :   22
%              Number of atoms          :  656 (3132 expanded)
%              Number of equality atoms :   83 ( 444 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t23_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( C
          = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
       => ( ( ( k1_relat_1 @ C )
            = ( k1_tarski @ A ) )
          & ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( C
            = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
         => ( ( ( k1_relat_1 @ C )
              = ( k1_tarski @ A ) )
            & ( ( k2_relat_1 @ C )
              = ( k1_tarski @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_relat_1])).

thf('0',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
    inference('sup+',[status(thm)],['0','2'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('4',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X30 @ X27 ) @ ( sk_C_2 @ X30 @ X27 ) ) @ X27 )
      | ( r2_hidden @ ( sk_C_2 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('5',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X13 = X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_3 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ sk_C_3 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_2 @ X0 @ sk_C_3 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('12',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = sk_B )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = sk_B ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('15',plain,
    ( ( ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 )
      = sk_B )
    | ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
    inference('sup+',[status(thm)],['0','2'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X23 @ X20 ) @ ( sk_D @ X23 @ X20 ) ) @ X20 )
      | ( r2_hidden @ ( sk_C_1 @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('20',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 = X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X3 = X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_3 )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_3 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_1 @ X0 @ sk_C_3 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = sk_A )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference(eq_fact,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_C_3 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_C_3 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['28'])).

thf('31',plain,(
    ! [X20: $i,X23: $i,X24: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X23 @ X20 ) @ X24 ) @ X20 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_C_3 ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_C_3 ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['18','37'])).

thf('39',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_relat_1 @ sk_C_3 ) )
   <= ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf('43',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['17','43'])).

thf('45',plain,
    ( ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['15','44'])).

thf('46',plain,(
    ! [X27: $i,X30: $i,X31: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_C_2 @ X30 @ X27 ) ) @ X27 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 )
      | ~ ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['15','44'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['17','43'])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 ) ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference('sup-',[status(thm)],['3','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bgPYCBJ2cQ
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:32:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.80/2.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.80/2.06  % Solved by: fo/fo7.sh
% 1.80/2.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.80/2.06  % done 1722 iterations in 1.602s
% 1.80/2.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.80/2.06  % SZS output start Refutation
% 1.80/2.06  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.80/2.06  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.80/2.06  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.80/2.06  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 1.80/2.06  thf(sk_A_type, type, sk_A: $i).
% 1.80/2.06  thf(sk_B_type, type, sk_B: $i).
% 1.80/2.06  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.80/2.06  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.80/2.06  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.80/2.06  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.80/2.06  thf(sk_C_3_type, type, sk_C_3: $i).
% 1.80/2.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.80/2.06  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 1.80/2.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.80/2.06  thf(t23_relat_1, conjecture,
% 1.80/2.06    (![A:$i,B:$i,C:$i]:
% 1.80/2.06     ( ( v1_relat_1 @ C ) =>
% 1.80/2.06       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 1.80/2.06         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 1.80/2.06           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 1.80/2.06  thf(zf_stmt_0, negated_conjecture,
% 1.80/2.06    (~( ![A:$i,B:$i,C:$i]:
% 1.80/2.06        ( ( v1_relat_1 @ C ) =>
% 1.80/2.06          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 1.80/2.06            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 1.80/2.06              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 1.80/2.06    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 1.80/2.06  thf('0', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 1.80/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.06  thf(d1_tarski, axiom,
% 1.80/2.06    (![A:$i,B:$i]:
% 1.80/2.06     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.80/2.06       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.80/2.06  thf('1', plain,
% 1.80/2.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/2.06         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 1.80/2.06      inference('cnf', [status(esa)], [d1_tarski])).
% 1.80/2.06  thf('2', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.80/2.06      inference('simplify', [status(thm)], ['1'])).
% 1.80/2.06  thf('3', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 1.80/2.06      inference('sup+', [status(thm)], ['0', '2'])).
% 1.80/2.06  thf(d5_relat_1, axiom,
% 1.80/2.06    (![A:$i,B:$i]:
% 1.80/2.06     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.80/2.06       ( ![C:$i]:
% 1.80/2.06         ( ( r2_hidden @ C @ B ) <=>
% 1.80/2.06           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 1.80/2.06  thf('4', plain,
% 1.80/2.06      (![X27 : $i, X30 : $i]:
% 1.80/2.06         (((X30) = (k2_relat_1 @ X27))
% 1.80/2.06          | (r2_hidden @ 
% 1.80/2.06             (k4_tarski @ (sk_D_2 @ X30 @ X27) @ (sk_C_2 @ X30 @ X27)) @ X27)
% 1.80/2.06          | (r2_hidden @ (sk_C_2 @ X30 @ X27) @ X30))),
% 1.80/2.06      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.80/2.06  thf('5', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 1.80/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.06  thf(t35_zfmisc_1, axiom,
% 1.80/2.06    (![A:$i,B:$i]:
% 1.80/2.06     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.80/2.06       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 1.80/2.06  thf('6', plain,
% 1.80/2.06      (![X16 : $i, X17 : $i]:
% 1.80/2.06         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 1.80/2.06           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 1.80/2.06      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 1.80/2.06  thf(t129_zfmisc_1, axiom,
% 1.80/2.06    (![A:$i,B:$i,C:$i,D:$i]:
% 1.80/2.06     ( ( r2_hidden @
% 1.80/2.06         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 1.80/2.06       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 1.80/2.06  thf('7', plain,
% 1.80/2.06      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.80/2.06         (((X13) = (X14))
% 1.80/2.06          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 1.80/2.06               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 1.80/2.06      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 1.80/2.06  thf('8', plain,
% 1.80/2.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.80/2.06         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 1.80/2.06             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 1.80/2.06          | ((X2) = (X0)))),
% 1.80/2.06      inference('sup-', [status(thm)], ['6', '7'])).
% 1.80/2.06  thf('9', plain,
% 1.80/2.06      (![X0 : $i, X1 : $i]:
% 1.80/2.06         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_3) | ((X0) = (sk_B)))),
% 1.80/2.06      inference('sup-', [status(thm)], ['5', '8'])).
% 1.80/2.06  thf('10', plain,
% 1.80/2.06      (![X0 : $i]:
% 1.80/2.06         ((r2_hidden @ (sk_C_2 @ X0 @ sk_C_3) @ X0)
% 1.80/2.06          | ((X0) = (k2_relat_1 @ sk_C_3))
% 1.80/2.06          | ((sk_C_2 @ X0 @ sk_C_3) = (sk_B)))),
% 1.80/2.06      inference('sup-', [status(thm)], ['4', '9'])).
% 1.80/2.06  thf('11', plain,
% 1.80/2.06      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.80/2.06         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 1.80/2.06      inference('cnf', [status(esa)], [d1_tarski])).
% 1.80/2.06  thf('12', plain,
% 1.80/2.06      (![X0 : $i, X3 : $i]:
% 1.80/2.06         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 1.80/2.06      inference('simplify', [status(thm)], ['11'])).
% 1.80/2.06  thf('13', plain,
% 1.80/2.06      (![X0 : $i]:
% 1.80/2.06         (((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (sk_B))
% 1.80/2.06          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_3))
% 1.80/2.06          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (X0)))),
% 1.80/2.06      inference('sup-', [status(thm)], ['10', '12'])).
% 1.80/2.06  thf('14', plain,
% 1.80/2.06      (![X0 : $i]:
% 1.80/2.06         (((X0) != (sk_B))
% 1.80/2.06          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_3))
% 1.80/2.06          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (sk_B)))),
% 1.80/2.06      inference('eq_fact', [status(thm)], ['13'])).
% 1.80/2.06  thf('15', plain,
% 1.80/2.06      ((((sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) = (sk_B))
% 1.80/2.06        | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 1.80/2.06      inference('simplify', [status(thm)], ['14'])).
% 1.80/2.06  thf('16', plain,
% 1.80/2.06      ((((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A))
% 1.80/2.06        | ((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B)))),
% 1.80/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.06  thf('17', plain,
% 1.80/2.06      ((((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B)))
% 1.80/2.06         <= (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B))))),
% 1.80/2.06      inference('split', [status(esa)], ['16'])).
% 1.80/2.06  thf('18', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 1.80/2.06      inference('sup+', [status(thm)], ['0', '2'])).
% 1.80/2.06  thf(d4_relat_1, axiom,
% 1.80/2.06    (![A:$i,B:$i]:
% 1.80/2.06     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 1.80/2.06       ( ![C:$i]:
% 1.80/2.06         ( ( r2_hidden @ C @ B ) <=>
% 1.80/2.06           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 1.80/2.06  thf('19', plain,
% 1.80/2.06      (![X20 : $i, X23 : $i]:
% 1.80/2.06         (((X23) = (k1_relat_1 @ X20))
% 1.80/2.06          | (r2_hidden @ 
% 1.80/2.06             (k4_tarski @ (sk_C_1 @ X23 @ X20) @ (sk_D @ X23 @ X20)) @ X20)
% 1.80/2.06          | (r2_hidden @ (sk_C_1 @ X23 @ X20) @ X23))),
% 1.80/2.06      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.80/2.06  thf('20', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 1.80/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.06  thf('21', plain,
% 1.80/2.06      (![X16 : $i, X17 : $i]:
% 1.80/2.06         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 1.80/2.06           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 1.80/2.06      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 1.80/2.06  thf(t128_zfmisc_1, axiom,
% 1.80/2.06    (![A:$i,B:$i,C:$i,D:$i]:
% 1.80/2.06     ( ( r2_hidden @
% 1.80/2.06         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 1.80/2.06       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 1.80/2.06  thf('22', plain,
% 1.80/2.06      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.80/2.06         (((X7) = (X6))
% 1.80/2.06          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ 
% 1.80/2.06               (k2_zfmisc_1 @ (k1_tarski @ X6) @ X9)))),
% 1.80/2.06      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 1.80/2.06  thf('23', plain,
% 1.80/2.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.80/2.06         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 1.80/2.06             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 1.80/2.06          | ((X3) = (X1)))),
% 1.80/2.06      inference('sup-', [status(thm)], ['21', '22'])).
% 1.80/2.06  thf('24', plain,
% 1.80/2.06      (![X0 : $i, X1 : $i]:
% 1.80/2.06         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_3) | ((X1) = (sk_A)))),
% 1.80/2.06      inference('sup-', [status(thm)], ['20', '23'])).
% 1.80/2.06  thf('25', plain,
% 1.80/2.06      (![X0 : $i]:
% 1.80/2.06         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_3) @ X0)
% 1.80/2.06          | ((X0) = (k1_relat_1 @ sk_C_3))
% 1.80/2.06          | ((sk_C_1 @ X0 @ sk_C_3) = (sk_A)))),
% 1.80/2.06      inference('sup-', [status(thm)], ['19', '24'])).
% 1.80/2.06  thf('26', plain,
% 1.80/2.06      (![X0 : $i, X3 : $i]:
% 1.80/2.06         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 1.80/2.06      inference('simplify', [status(thm)], ['11'])).
% 1.80/2.06  thf('27', plain,
% 1.80/2.06      (![X0 : $i]:
% 1.80/2.06         (((sk_C_1 @ (k1_tarski @ X0) @ sk_C_3) = (sk_A))
% 1.80/2.06          | ((k1_tarski @ X0) = (k1_relat_1 @ sk_C_3))
% 1.80/2.06          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_3) = (X0)))),
% 1.80/2.06      inference('sup-', [status(thm)], ['25', '26'])).
% 1.80/2.06  thf('28', plain,
% 1.80/2.06      (![X0 : $i]:
% 1.80/2.06         (((sk_A) != (X0))
% 1.80/2.06          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_3) = (X0))
% 1.80/2.06          | ((k1_tarski @ X0) = (k1_relat_1 @ sk_C_3)))),
% 1.80/2.06      inference('eq_fact', [status(thm)], ['27'])).
% 1.80/2.06  thf('29', plain,
% 1.80/2.06      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 1.80/2.06        | ((sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) = (sk_A)))),
% 1.80/2.06      inference('simplify', [status(thm)], ['28'])).
% 1.80/2.06  thf('30', plain,
% 1.80/2.06      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 1.80/2.06        | ((sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) = (sk_A)))),
% 1.80/2.06      inference('simplify', [status(thm)], ['28'])).
% 1.80/2.06  thf('31', plain,
% 1.80/2.06      (![X20 : $i, X23 : $i, X24 : $i]:
% 1.80/2.06         (((X23) = (k1_relat_1 @ X20))
% 1.80/2.06          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X23 @ X20) @ X24) @ X20)
% 1.80/2.06          | ~ (r2_hidden @ (sk_C_1 @ X23 @ X20) @ X23))),
% 1.80/2.06      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.80/2.06  thf('32', plain,
% 1.80/2.06      (![X0 : $i]:
% 1.80/2.06         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 1.80/2.06          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 1.80/2.06          | ~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) @ 
% 1.80/2.06               (k1_tarski @ sk_A))
% 1.80/2.06          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 1.80/2.06      inference('sup-', [status(thm)], ['30', '31'])).
% 1.80/2.06  thf('33', plain,
% 1.80/2.06      (![X0 : $i]:
% 1.80/2.06         (~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) @ 
% 1.80/2.06             (k1_tarski @ sk_A))
% 1.80/2.06          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 1.80/2.06          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3))),
% 1.80/2.06      inference('simplify', [status(thm)], ['32'])).
% 1.80/2.06  thf('34', plain,
% 1.80/2.06      (![X0 : $i]:
% 1.80/2.06         (~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 1.80/2.06          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 1.80/2.06          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 1.80/2.06          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 1.80/2.06      inference('sup-', [status(thm)], ['29', '33'])).
% 1.80/2.06  thf('35', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.80/2.06      inference('simplify', [status(thm)], ['1'])).
% 1.80/2.06  thf('36', plain,
% 1.80/2.06      (![X0 : $i]:
% 1.80/2.06         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 1.80/2.06          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 1.80/2.06          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 1.80/2.06      inference('demod', [status(thm)], ['34', '35'])).
% 1.80/2.06  thf('37', plain,
% 1.80/2.06      (![X0 : $i]:
% 1.80/2.06         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 1.80/2.06          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 1.80/2.06      inference('simplify', [status(thm)], ['36'])).
% 1.80/2.06  thf('38', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))),
% 1.80/2.06      inference('sup-', [status(thm)], ['18', '37'])).
% 1.80/2.06  thf('39', plain,
% 1.80/2.06      ((((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A)))
% 1.80/2.06         <= (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))))),
% 1.80/2.06      inference('split', [status(esa)], ['16'])).
% 1.80/2.06  thf('40', plain,
% 1.80/2.06      ((((k1_relat_1 @ sk_C_3) != (k1_relat_1 @ sk_C_3)))
% 1.80/2.06         <= (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))))),
% 1.80/2.06      inference('sup-', [status(thm)], ['38', '39'])).
% 1.80/2.06  thf('41', plain, ((((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A)))),
% 1.80/2.06      inference('simplify', [status(thm)], ['40'])).
% 1.80/2.06  thf('42', plain,
% 1.80/2.06      (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B))) | 
% 1.80/2.06       ~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A)))),
% 1.80/2.06      inference('split', [status(esa)], ['16'])).
% 1.80/2.06  thf('43', plain, (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B)))),
% 1.80/2.06      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 1.80/2.06  thf('44', plain, (((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B))),
% 1.80/2.06      inference('simpl_trail', [status(thm)], ['17', '43'])).
% 1.80/2.06  thf('45', plain, (((sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) = (sk_B))),
% 1.80/2.06      inference('simplify_reflect-', [status(thm)], ['15', '44'])).
% 1.80/2.06  thf('46', plain,
% 1.80/2.06      (![X27 : $i, X30 : $i, X31 : $i]:
% 1.80/2.06         (((X30) = (k2_relat_1 @ X27))
% 1.80/2.06          | ~ (r2_hidden @ (k4_tarski @ X31 @ (sk_C_2 @ X30 @ X27)) @ X27)
% 1.80/2.06          | ~ (r2_hidden @ (sk_C_2 @ X30 @ X27) @ X30))),
% 1.80/2.06      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.80/2.06  thf('47', plain,
% 1.80/2.06      (![X0 : $i]:
% 1.80/2.06         (~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)
% 1.80/2.06          | ~ (r2_hidden @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) @ 
% 1.80/2.06               (k1_tarski @ sk_B))
% 1.80/2.06          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 1.80/2.06      inference('sup-', [status(thm)], ['45', '46'])).
% 1.80/2.06  thf('48', plain, (((sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) = (sk_B))),
% 1.80/2.06      inference('simplify_reflect-', [status(thm)], ['15', '44'])).
% 1.80/2.06  thf('49', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.80/2.06      inference('simplify', [status(thm)], ['1'])).
% 1.80/2.06  thf('50', plain,
% 1.80/2.06      (![X0 : $i]:
% 1.80/2.06         (~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)
% 1.80/2.06          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 1.80/2.06      inference('demod', [status(thm)], ['47', '48', '49'])).
% 1.80/2.06  thf('51', plain, (((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B))),
% 1.80/2.06      inference('simpl_trail', [status(thm)], ['17', '43'])).
% 1.80/2.06  thf('52', plain,
% 1.80/2.06      (![X0 : $i]: ~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)),
% 1.80/2.06      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 1.80/2.06  thf('53', plain, ($false), inference('sup-', [status(thm)], ['3', '52'])).
% 1.80/2.06  
% 1.80/2.06  % SZS output end Refutation
% 1.80/2.06  
% 1.80/2.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
