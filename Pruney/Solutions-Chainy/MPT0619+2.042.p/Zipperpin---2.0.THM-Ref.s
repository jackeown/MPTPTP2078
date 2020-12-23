%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uqEI1ND0RS

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:25 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 163 expanded)
%              Number of leaves         :   19 (  54 expanded)
%              Depth                    :   19
%              Number of atoms          :  643 (1925 expanded)
%              Number of equality atoms :   59 ( 205 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('1',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X15: $i] :
      ( ( ( k9_relat_1 @ X15 @ ( k1_relat_1 @ X15 ) )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('3',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X12 @ X13 ) @ X12 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_tarski @ sk_A ) @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_tarski @ sk_A ) @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_tarski @ sk_A ) @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

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
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = X0 )
      | ( ( sk_D @ sk_B @ ( k1_tarski @ sk_A ) @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X14 @ X12 @ X13 ) @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ ( k1_tarski @ sk_A ) @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 ) ) @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 ) ) @ sk_B )
      | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ X19 )
      | ( X20
        = ( k1_funct_1 @ X19 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 )
        = X0 ) ) ),
    inference(eq_fact,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
       != X0 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('33',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X17 @ X16 ) @ ( k2_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,
    ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('44',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_A )
     != ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','42','43'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uqEI1ND0RS
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:05:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.51/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.71  % Solved by: fo/fo7.sh
% 0.51/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.71  % done 405 iterations in 0.267s
% 0.51/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.71  % SZS output start Refutation
% 0.51/0.71  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.51/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.51/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.71  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.51/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.71  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.51/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.71  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.51/0.71  thf(d1_tarski, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.51/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.51/0.71  thf('0', plain,
% 0.51/0.71      (![X0 : $i, X4 : $i]:
% 0.51/0.71         (((X4) = (k1_tarski @ X0))
% 0.51/0.71          | ((sk_C @ X4 @ X0) = (X0))
% 0.51/0.71          | (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.51/0.71      inference('cnf', [status(esa)], [d1_tarski])).
% 0.51/0.71  thf(t14_funct_1, conjecture,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.71       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.51/0.71         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.51/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.71    (~( ![A:$i,B:$i]:
% 0.51/0.71        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.71          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.51/0.71            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.51/0.71    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.51/0.71  thf('1', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf(t146_relat_1, axiom,
% 0.51/0.71    (![A:$i]:
% 0.51/0.71     ( ( v1_relat_1 @ A ) =>
% 0.51/0.71       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.51/0.71  thf('2', plain,
% 0.51/0.71      (![X15 : $i]:
% 0.51/0.71         (((k9_relat_1 @ X15 @ (k1_relat_1 @ X15)) = (k2_relat_1 @ X15))
% 0.51/0.71          | ~ (v1_relat_1 @ X15))),
% 0.51/0.71      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.51/0.71  thf('3', plain,
% 0.51/0.71      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.51/0.71        | ~ (v1_relat_1 @ sk_B))),
% 0.51/0.71      inference('sup+', [status(thm)], ['1', '2'])).
% 0.51/0.71  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('5', plain,
% 0.51/0.71      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 0.51/0.71      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.71  thf(t143_relat_1, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i]:
% 0.51/0.71     ( ( v1_relat_1 @ C ) =>
% 0.51/0.71       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.51/0.71         ( ?[D:$i]:
% 0.51/0.71           ( ( r2_hidden @ D @ B ) & 
% 0.51/0.71             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.51/0.71             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.51/0.71  thf('6', plain,
% 0.51/0.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 0.51/0.71          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ X12)
% 0.51/0.71          | ~ (v1_relat_1 @ X14))),
% 0.51/0.71      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.51/0.71  thf('7', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.51/0.71          | ~ (v1_relat_1 @ sk_B)
% 0.51/0.71          | (r2_hidden @ (sk_D @ sk_B @ (k1_tarski @ sk_A) @ X0) @ 
% 0.51/0.71             (k1_tarski @ sk_A)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.51/0.71  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('9', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.51/0.71          | (r2_hidden @ (sk_D @ sk_B @ (k1_tarski @ sk_A) @ X0) @ 
% 0.51/0.71             (k1_tarski @ sk_A)))),
% 0.51/0.71      inference('demod', [status(thm)], ['7', '8'])).
% 0.51/0.71  thf('10', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         (((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (X0))
% 0.51/0.71          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.51/0.71          | (r2_hidden @ 
% 0.51/0.71             (sk_D @ sk_B @ (k1_tarski @ sk_A) @ 
% 0.51/0.71              (sk_C @ (k2_relat_1 @ sk_B) @ X0)) @ 
% 0.51/0.71             (k1_tarski @ sk_A)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['0', '9'])).
% 0.51/0.71  thf('11', plain,
% 0.51/0.71      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.51/0.71      inference('cnf', [status(esa)], [d1_tarski])).
% 0.51/0.71  thf('12', plain,
% 0.51/0.71      (![X0 : $i, X3 : $i]:
% 0.51/0.71         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.51/0.71      inference('simplify', [status(thm)], ['11'])).
% 0.51/0.71  thf('13', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.51/0.71          | ((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (X0))
% 0.51/0.71          | ((sk_D @ sk_B @ (k1_tarski @ sk_A) @ 
% 0.51/0.71              (sk_C @ (k2_relat_1 @ sk_B) @ X0)) = (sk_A)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['10', '12'])).
% 0.51/0.71  thf('14', plain,
% 0.51/0.71      (![X0 : $i, X4 : $i]:
% 0.51/0.71         (((X4) = (k1_tarski @ X0))
% 0.51/0.71          | ((sk_C @ X4 @ X0) = (X0))
% 0.51/0.71          | (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.51/0.71      inference('cnf', [status(esa)], [d1_tarski])).
% 0.51/0.71  thf('15', plain,
% 0.51/0.71      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 0.51/0.71      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.71  thf('16', plain,
% 0.51/0.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 0.51/0.71          | (r2_hidden @ (k4_tarski @ (sk_D @ X14 @ X12 @ X13) @ X13) @ X14)
% 0.51/0.71          | ~ (v1_relat_1 @ X14))),
% 0.51/0.71      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.51/0.71  thf('17', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.51/0.71          | ~ (v1_relat_1 @ sk_B)
% 0.51/0.71          | (r2_hidden @ 
% 0.51/0.71             (k4_tarski @ (sk_D @ sk_B @ (k1_tarski @ sk_A) @ X0) @ X0) @ sk_B))),
% 0.51/0.71      inference('sup-', [status(thm)], ['15', '16'])).
% 0.51/0.71  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('19', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.51/0.71          | (r2_hidden @ 
% 0.51/0.71             (k4_tarski @ (sk_D @ sk_B @ (k1_tarski @ sk_A) @ X0) @ X0) @ sk_B))),
% 0.51/0.71      inference('demod', [status(thm)], ['17', '18'])).
% 0.51/0.71  thf('20', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         (((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (X0))
% 0.51/0.71          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.51/0.71          | (r2_hidden @ 
% 0.51/0.71             (k4_tarski @ 
% 0.51/0.71              (sk_D @ sk_B @ (k1_tarski @ sk_A) @ 
% 0.51/0.71               (sk_C @ (k2_relat_1 @ sk_B) @ X0)) @ 
% 0.51/0.71              (sk_C @ (k2_relat_1 @ sk_B) @ X0)) @ 
% 0.51/0.71             sk_B))),
% 0.51/0.71      inference('sup-', [status(thm)], ['14', '19'])).
% 0.51/0.71  thf('21', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         ((r2_hidden @ 
% 0.51/0.71           (k4_tarski @ sk_A @ (sk_C @ (k2_relat_1 @ sk_B) @ X0)) @ sk_B)
% 0.51/0.71          | ((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (X0))
% 0.51/0.71          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.51/0.71          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.51/0.71          | ((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (X0)))),
% 0.51/0.71      inference('sup+', [status(thm)], ['13', '20'])).
% 0.51/0.71  thf('22', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.51/0.71          | ((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (X0))
% 0.51/0.71          | (r2_hidden @ 
% 0.51/0.71             (k4_tarski @ sk_A @ (sk_C @ (k2_relat_1 @ sk_B) @ X0)) @ sk_B))),
% 0.51/0.71      inference('simplify', [status(thm)], ['21'])).
% 0.51/0.71  thf(t8_funct_1, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i]:
% 0.51/0.71     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.51/0.71       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.51/0.71         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.51/0.71           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.51/0.71  thf('23', plain,
% 0.51/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.51/0.71         (~ (r2_hidden @ (k4_tarski @ X18 @ X20) @ X19)
% 0.51/0.71          | ((X20) = (k1_funct_1 @ X19 @ X18))
% 0.51/0.71          | ~ (v1_funct_1 @ X19)
% 0.51/0.71          | ~ (v1_relat_1 @ X19))),
% 0.51/0.71      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.51/0.71  thf('24', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         (((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (X0))
% 0.51/0.71          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.51/0.71          | ~ (v1_relat_1 @ sk_B)
% 0.51/0.71          | ~ (v1_funct_1 @ sk_B)
% 0.51/0.71          | ((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['22', '23'])).
% 0.51/0.71  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('27', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         (((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (X0))
% 0.51/0.71          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.51/0.71          | ((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.51/0.71      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.51/0.71  thf('28', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.51/0.71          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.51/0.71          | ((sk_C @ (k2_relat_1 @ sk_B) @ X0) = (X0)))),
% 0.51/0.71      inference('eq_fact', [status(thm)], ['27'])).
% 0.51/0.71  thf('29', plain,
% 0.51/0.71      ((((sk_C @ (k2_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.51/0.71          = (k1_funct_1 @ sk_B @ sk_A))
% 0.51/0.71        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.51/0.71      inference('simplify', [status(thm)], ['28'])).
% 0.51/0.71  thf('30', plain,
% 0.51/0.71      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('31', plain,
% 0.51/0.71      (((sk_C @ (k2_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.51/0.71         = (k1_funct_1 @ sk_B @ sk_A))),
% 0.51/0.71      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.51/0.71  thf('32', plain,
% 0.51/0.71      (![X0 : $i, X4 : $i]:
% 0.51/0.71         (((X4) = (k1_tarski @ X0))
% 0.51/0.71          | ((sk_C @ X4 @ X0) != (X0))
% 0.51/0.71          | ~ (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.51/0.71      inference('cnf', [status(esa)], [d1_tarski])).
% 0.51/0.71  thf('33', plain,
% 0.51/0.71      ((~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.51/0.71        | ((sk_C @ (k2_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.51/0.71            != (k1_funct_1 @ sk_B @ sk_A))
% 0.51/0.71        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.51/0.71      inference('sup-', [status(thm)], ['31', '32'])).
% 0.51/0.71  thf('34', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.71         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.51/0.71      inference('cnf', [status(esa)], [d1_tarski])).
% 0.51/0.71  thf('35', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.51/0.71      inference('simplify', [status(thm)], ['34'])).
% 0.51/0.71  thf('36', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf(t12_funct_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.71       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.51/0.71         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.51/0.71  thf('37', plain,
% 0.51/0.71      (![X16 : $i, X17 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.51/0.71          | (r2_hidden @ (k1_funct_1 @ X17 @ X16) @ (k2_relat_1 @ X17))
% 0.51/0.71          | ~ (v1_funct_1 @ X17)
% 0.51/0.71          | ~ (v1_relat_1 @ X17))),
% 0.51/0.71      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.51/0.71  thf('38', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.51/0.71          | ~ (v1_relat_1 @ sk_B)
% 0.51/0.71          | ~ (v1_funct_1 @ sk_B)
% 0.51/0.71          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.71  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('41', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.51/0.71          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.51/0.71      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.51/0.71  thf('42', plain,
% 0.51/0.71      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.51/0.71      inference('sup-', [status(thm)], ['35', '41'])).
% 0.51/0.71  thf('43', plain,
% 0.51/0.71      (((sk_C @ (k2_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.51/0.71         = (k1_funct_1 @ sk_B @ sk_A))),
% 0.51/0.71      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.51/0.71  thf('44', plain,
% 0.51/0.71      ((((k1_funct_1 @ sk_B @ sk_A) != (k1_funct_1 @ sk_B @ sk_A))
% 0.51/0.71        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.51/0.71      inference('demod', [status(thm)], ['33', '42', '43'])).
% 0.51/0.71  thf('45', plain,
% 0.51/0.71      (((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.51/0.71      inference('simplify', [status(thm)], ['44'])).
% 0.51/0.71  thf('46', plain,
% 0.51/0.71      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('47', plain, ($false),
% 0.51/0.71      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.51/0.71  
% 0.51/0.71  % SZS output end Refutation
% 0.51/0.71  
% 0.51/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
