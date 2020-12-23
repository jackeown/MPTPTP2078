%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.njVf9kMS58

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:43 EST 2020

% Result     : Theorem 2.78s
% Output     : Refutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 278 expanded)
%              Number of leaves         :   21 (  79 expanded)
%              Depth                    :   22
%              Number of atoms          :  658 (3144 expanded)
%              Number of equality atoms :   84 ( 450 expanded)
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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X8 = X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ ( k1_tarski @ X9 ) ) ) ) ),
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

thf(t34_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 = X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 = X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ ( k1_tarski @ ( k4_tarski @ X11 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.njVf9kMS58
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:14:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.78/3.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.78/3.02  % Solved by: fo/fo7.sh
% 2.78/3.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.78/3.02  % done 1140 iterations in 2.569s
% 2.78/3.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.78/3.02  % SZS output start Refutation
% 2.78/3.02  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.78/3.02  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.78/3.02  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.78/3.02  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 2.78/3.02  thf(sk_A_type, type, sk_A: $i).
% 2.78/3.02  thf(sk_B_type, type, sk_B: $i).
% 2.78/3.02  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 2.78/3.02  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.78/3.02  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.78/3.02  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.78/3.02  thf(sk_C_3_type, type, sk_C_3: $i).
% 2.78/3.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.78/3.02  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 2.78/3.02  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.78/3.02  thf(t23_relat_1, conjecture,
% 2.78/3.02    (![A:$i,B:$i,C:$i]:
% 2.78/3.02     ( ( v1_relat_1 @ C ) =>
% 2.78/3.02       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 2.78/3.02         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 2.78/3.02           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 2.78/3.02  thf(zf_stmt_0, negated_conjecture,
% 2.78/3.02    (~( ![A:$i,B:$i,C:$i]:
% 2.78/3.02        ( ( v1_relat_1 @ C ) =>
% 2.78/3.02          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 2.78/3.02            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 2.78/3.02              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 2.78/3.02    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 2.78/3.02  thf('0', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 2.78/3.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/3.02  thf(d1_tarski, axiom,
% 2.78/3.02    (![A:$i,B:$i]:
% 2.78/3.02     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 2.78/3.02       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 2.78/3.02  thf('1', plain,
% 2.78/3.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.78/3.02         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 2.78/3.02      inference('cnf', [status(esa)], [d1_tarski])).
% 2.78/3.02  thf('2', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.78/3.02      inference('simplify', [status(thm)], ['1'])).
% 2.78/3.02  thf('3', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 2.78/3.02      inference('sup+', [status(thm)], ['0', '2'])).
% 2.78/3.02  thf(d5_relat_1, axiom,
% 2.78/3.02    (![A:$i,B:$i]:
% 2.78/3.02     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 2.78/3.02       ( ![C:$i]:
% 2.78/3.02         ( ( r2_hidden @ C @ B ) <=>
% 2.78/3.02           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 2.78/3.02  thf('4', plain,
% 2.78/3.02      (![X27 : $i, X30 : $i]:
% 2.78/3.02         (((X30) = (k2_relat_1 @ X27))
% 2.78/3.02          | (r2_hidden @ 
% 2.78/3.02             (k4_tarski @ (sk_D_2 @ X30 @ X27) @ (sk_C_2 @ X30 @ X27)) @ X27)
% 2.78/3.02          | (r2_hidden @ (sk_C_2 @ X30 @ X27) @ X30))),
% 2.78/3.02      inference('cnf', [status(esa)], [d5_relat_1])).
% 2.78/3.02  thf('5', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 2.78/3.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/3.02  thf(t35_zfmisc_1, axiom,
% 2.78/3.02    (![A:$i,B:$i]:
% 2.78/3.02     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 2.78/3.02       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 2.78/3.02  thf('6', plain,
% 2.78/3.02      (![X16 : $i, X17 : $i]:
% 2.78/3.02         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 2.78/3.02           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 2.78/3.02      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 2.78/3.02  thf(t129_zfmisc_1, axiom,
% 2.78/3.02    (![A:$i,B:$i,C:$i,D:$i]:
% 2.78/3.02     ( ( r2_hidden @
% 2.78/3.02         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 2.78/3.02       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 2.78/3.02  thf('7', plain,
% 2.78/3.02      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.78/3.02         (((X8) = (X9))
% 2.78/3.02          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 2.78/3.02               (k2_zfmisc_1 @ X7 @ (k1_tarski @ X9))))),
% 2.78/3.02      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 2.78/3.02  thf('8', plain,
% 2.78/3.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.78/3.02         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 2.78/3.02             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 2.78/3.02          | ((X2) = (X0)))),
% 2.78/3.02      inference('sup-', [status(thm)], ['6', '7'])).
% 2.78/3.02  thf('9', plain,
% 2.78/3.02      (![X0 : $i, X1 : $i]:
% 2.78/3.02         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_3) | ((X0) = (sk_B)))),
% 2.78/3.02      inference('sup-', [status(thm)], ['5', '8'])).
% 2.78/3.02  thf('10', plain,
% 2.78/3.02      (![X0 : $i]:
% 2.78/3.02         ((r2_hidden @ (sk_C_2 @ X0 @ sk_C_3) @ X0)
% 2.78/3.02          | ((X0) = (k2_relat_1 @ sk_C_3))
% 2.78/3.02          | ((sk_C_2 @ X0 @ sk_C_3) = (sk_B)))),
% 2.78/3.02      inference('sup-', [status(thm)], ['4', '9'])).
% 2.78/3.02  thf('11', plain,
% 2.78/3.02      (![X0 : $i, X2 : $i, X3 : $i]:
% 2.78/3.02         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 2.78/3.02      inference('cnf', [status(esa)], [d1_tarski])).
% 2.78/3.02  thf('12', plain,
% 2.78/3.02      (![X0 : $i, X3 : $i]:
% 2.78/3.02         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 2.78/3.02      inference('simplify', [status(thm)], ['11'])).
% 2.78/3.02  thf('13', plain,
% 2.78/3.02      (![X0 : $i]:
% 2.78/3.02         (((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (sk_B))
% 2.78/3.02          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_3))
% 2.78/3.02          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (X0)))),
% 2.78/3.02      inference('sup-', [status(thm)], ['10', '12'])).
% 2.78/3.02  thf('14', plain,
% 2.78/3.02      (![X0 : $i]:
% 2.78/3.02         (((X0) != (sk_B))
% 2.78/3.02          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_3))
% 2.78/3.02          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (sk_B)))),
% 2.78/3.02      inference('eq_fact', [status(thm)], ['13'])).
% 2.78/3.02  thf('15', plain,
% 2.78/3.02      ((((sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) = (sk_B))
% 2.78/3.02        | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 2.78/3.02      inference('simplify', [status(thm)], ['14'])).
% 2.78/3.02  thf('16', plain,
% 2.78/3.02      ((((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A))
% 2.78/3.02        | ((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B)))),
% 2.78/3.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/3.02  thf('17', plain,
% 2.78/3.02      ((((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B)))
% 2.78/3.02         <= (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B))))),
% 2.78/3.02      inference('split', [status(esa)], ['16'])).
% 2.78/3.02  thf('18', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 2.78/3.02      inference('sup+', [status(thm)], ['0', '2'])).
% 2.78/3.02  thf(d4_relat_1, axiom,
% 2.78/3.02    (![A:$i,B:$i]:
% 2.78/3.02     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 2.78/3.02       ( ![C:$i]:
% 2.78/3.02         ( ( r2_hidden @ C @ B ) <=>
% 2.78/3.02           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 2.78/3.02  thf('19', plain,
% 2.78/3.02      (![X20 : $i, X23 : $i]:
% 2.78/3.02         (((X23) = (k1_relat_1 @ X20))
% 2.78/3.02          | (r2_hidden @ 
% 2.78/3.02             (k4_tarski @ (sk_C_1 @ X23 @ X20) @ (sk_D @ X23 @ X20)) @ X20)
% 2.78/3.02          | (r2_hidden @ (sk_C_1 @ X23 @ X20) @ X23))),
% 2.78/3.02      inference('cnf', [status(esa)], [d4_relat_1])).
% 2.78/3.02  thf('20', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 2.78/3.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/3.02  thf(t34_zfmisc_1, axiom,
% 2.78/3.02    (![A:$i,B:$i,C:$i,D:$i]:
% 2.78/3.02     ( ( r2_hidden @
% 2.78/3.02         ( k4_tarski @ A @ B ) @ 
% 2.78/3.02         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 2.78/3.02       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 2.78/3.02  thf('21', plain,
% 2.78/3.02      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 2.78/3.02         (((X12) = (X11))
% 2.78/3.02          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ 
% 2.78/3.02               (k2_zfmisc_1 @ (k1_tarski @ X11) @ (k1_tarski @ X14))))),
% 2.78/3.02      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 2.78/3.02  thf('22', plain,
% 2.78/3.02      (![X16 : $i, X17 : $i]:
% 2.78/3.02         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 2.78/3.02           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 2.78/3.02      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 2.78/3.02  thf('23', plain,
% 2.78/3.02      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 2.78/3.02         (((X12) = (X11))
% 2.78/3.02          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ 
% 2.78/3.02               (k1_tarski @ (k4_tarski @ X11 @ X14))))),
% 2.78/3.02      inference('demod', [status(thm)], ['21', '22'])).
% 2.78/3.02  thf('24', plain,
% 2.78/3.02      (![X0 : $i, X1 : $i]:
% 2.78/3.02         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_3) | ((X1) = (sk_A)))),
% 2.78/3.02      inference('sup-', [status(thm)], ['20', '23'])).
% 2.78/3.02  thf('25', plain,
% 2.78/3.02      (![X0 : $i]:
% 2.78/3.02         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_3) @ X0)
% 2.78/3.02          | ((X0) = (k1_relat_1 @ sk_C_3))
% 2.78/3.02          | ((sk_C_1 @ X0 @ sk_C_3) = (sk_A)))),
% 2.78/3.02      inference('sup-', [status(thm)], ['19', '24'])).
% 2.78/3.02  thf('26', plain,
% 2.78/3.02      (![X0 : $i, X3 : $i]:
% 2.78/3.02         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 2.78/3.02      inference('simplify', [status(thm)], ['11'])).
% 2.78/3.02  thf('27', plain,
% 2.78/3.02      (![X0 : $i]:
% 2.78/3.02         (((sk_C_1 @ (k1_tarski @ X0) @ sk_C_3) = (sk_A))
% 2.78/3.02          | ((k1_tarski @ X0) = (k1_relat_1 @ sk_C_3))
% 2.78/3.02          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_3) = (X0)))),
% 2.78/3.02      inference('sup-', [status(thm)], ['25', '26'])).
% 2.78/3.02  thf('28', plain,
% 2.78/3.02      (![X0 : $i]:
% 2.78/3.02         (((sk_A) != (X0))
% 2.78/3.02          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_3) = (X0))
% 2.78/3.02          | ((k1_tarski @ X0) = (k1_relat_1 @ sk_C_3)))),
% 2.78/3.02      inference('eq_fact', [status(thm)], ['27'])).
% 2.78/3.02  thf('29', plain,
% 2.78/3.02      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 2.78/3.02        | ((sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) = (sk_A)))),
% 2.78/3.02      inference('simplify', [status(thm)], ['28'])).
% 2.78/3.02  thf('30', plain,
% 2.78/3.02      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 2.78/3.02        | ((sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) = (sk_A)))),
% 2.78/3.02      inference('simplify', [status(thm)], ['28'])).
% 2.78/3.02  thf('31', plain,
% 2.78/3.02      (![X20 : $i, X23 : $i, X24 : $i]:
% 2.78/3.02         (((X23) = (k1_relat_1 @ X20))
% 2.78/3.02          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X23 @ X20) @ X24) @ X20)
% 2.78/3.02          | ~ (r2_hidden @ (sk_C_1 @ X23 @ X20) @ X23))),
% 2.78/3.02      inference('cnf', [status(esa)], [d4_relat_1])).
% 2.78/3.02  thf('32', plain,
% 2.78/3.02      (![X0 : $i]:
% 2.78/3.02         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 2.78/3.02          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 2.78/3.02          | ~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) @ 
% 2.78/3.02               (k1_tarski @ sk_A))
% 2.78/3.02          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 2.78/3.02      inference('sup-', [status(thm)], ['30', '31'])).
% 2.78/3.02  thf('33', plain,
% 2.78/3.02      (![X0 : $i]:
% 2.78/3.02         (~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) @ 
% 2.78/3.02             (k1_tarski @ sk_A))
% 2.78/3.02          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 2.78/3.02          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3))),
% 2.78/3.02      inference('simplify', [status(thm)], ['32'])).
% 2.78/3.02  thf('34', plain,
% 2.78/3.02      (![X0 : $i]:
% 2.78/3.02         (~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 2.78/3.02          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 2.78/3.02          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 2.78/3.02          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 2.78/3.02      inference('sup-', [status(thm)], ['29', '33'])).
% 2.78/3.02  thf('35', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.78/3.02      inference('simplify', [status(thm)], ['1'])).
% 2.78/3.02  thf('36', plain,
% 2.78/3.02      (![X0 : $i]:
% 2.78/3.02         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 2.78/3.02          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 2.78/3.02          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 2.78/3.02      inference('demod', [status(thm)], ['34', '35'])).
% 2.78/3.02  thf('37', plain,
% 2.78/3.02      (![X0 : $i]:
% 2.78/3.02         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 2.78/3.02          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 2.78/3.02      inference('simplify', [status(thm)], ['36'])).
% 2.78/3.02  thf('38', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))),
% 2.78/3.02      inference('sup-', [status(thm)], ['18', '37'])).
% 2.78/3.02  thf('39', plain,
% 2.78/3.02      ((((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A)))
% 2.78/3.02         <= (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))))),
% 2.78/3.02      inference('split', [status(esa)], ['16'])).
% 2.78/3.02  thf('40', plain,
% 2.78/3.02      ((((k1_relat_1 @ sk_C_3) != (k1_relat_1 @ sk_C_3)))
% 2.78/3.02         <= (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))))),
% 2.78/3.02      inference('sup-', [status(thm)], ['38', '39'])).
% 2.78/3.02  thf('41', plain, ((((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A)))),
% 2.78/3.02      inference('simplify', [status(thm)], ['40'])).
% 2.78/3.02  thf('42', plain,
% 2.78/3.02      (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B))) | 
% 2.78/3.02       ~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A)))),
% 2.78/3.02      inference('split', [status(esa)], ['16'])).
% 2.78/3.02  thf('43', plain, (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B)))),
% 2.78/3.02      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 2.78/3.02  thf('44', plain, (((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B))),
% 2.78/3.02      inference('simpl_trail', [status(thm)], ['17', '43'])).
% 2.78/3.02  thf('45', plain, (((sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) = (sk_B))),
% 2.78/3.02      inference('simplify_reflect-', [status(thm)], ['15', '44'])).
% 2.78/3.02  thf('46', plain,
% 2.78/3.02      (![X27 : $i, X30 : $i, X31 : $i]:
% 2.78/3.02         (((X30) = (k2_relat_1 @ X27))
% 2.78/3.02          | ~ (r2_hidden @ (k4_tarski @ X31 @ (sk_C_2 @ X30 @ X27)) @ X27)
% 2.78/3.02          | ~ (r2_hidden @ (sk_C_2 @ X30 @ X27) @ X30))),
% 2.78/3.02      inference('cnf', [status(esa)], [d5_relat_1])).
% 2.78/3.02  thf('47', plain,
% 2.78/3.02      (![X0 : $i]:
% 2.78/3.02         (~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)
% 2.78/3.02          | ~ (r2_hidden @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) @ 
% 2.78/3.02               (k1_tarski @ sk_B))
% 2.78/3.02          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 2.78/3.02      inference('sup-', [status(thm)], ['45', '46'])).
% 2.78/3.02  thf('48', plain, (((sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) = (sk_B))),
% 2.78/3.02      inference('simplify_reflect-', [status(thm)], ['15', '44'])).
% 2.78/3.02  thf('49', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.78/3.02      inference('simplify', [status(thm)], ['1'])).
% 2.78/3.02  thf('50', plain,
% 2.78/3.02      (![X0 : $i]:
% 2.78/3.02         (~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)
% 2.78/3.02          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 2.78/3.02      inference('demod', [status(thm)], ['47', '48', '49'])).
% 2.78/3.02  thf('51', plain, (((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B))),
% 2.78/3.02      inference('simpl_trail', [status(thm)], ['17', '43'])).
% 2.78/3.02  thf('52', plain,
% 2.78/3.02      (![X0 : $i]: ~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)),
% 2.78/3.02      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 2.78/3.02  thf('53', plain, ($false), inference('sup-', [status(thm)], ['3', '52'])).
% 2.78/3.02  
% 2.78/3.02  % SZS output end Refutation
% 2.78/3.02  
% 2.78/3.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
