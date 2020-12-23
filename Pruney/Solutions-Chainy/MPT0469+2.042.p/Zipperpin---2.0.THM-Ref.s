%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EjFLYbsFwe

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:22 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 155 expanded)
%              Number of leaves         :   27 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  451 (1070 expanded)
%              Number of equality atoms :   59 ( 149 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('0',plain,(
    ! [X31: $i,X34: $i] :
      ( ( X34
        = ( k2_relat_1 @ X31 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X34 @ X31 ) @ ( sk_C_1 @ X34 @ X31 ) ) @ X31 )
      | ( r2_hidden @ ( sk_C_1 @ X34 @ X31 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ ( k4_tarski @ ( sk_D_1 @ X1 @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( ( k1_tarski @ ( k4_tarski @ ( sk_D_1 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 != X19 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X19 ) )
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('6',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X19 ) )
     != ( k1_tarski @ X19 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('11',plain,(
    ! [X19: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X19 ) ) ),
    inference(demod,[status(thm)],['6','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('16',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( ( k1_tarski @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X19: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X19 ) ) ),
    inference(demod,[status(thm)],['6','9','10'])).

thf('18',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) )).

thf('20',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X36 ) @ ( k2_relat_1 @ X36 ) )
      | ~ ( r2_hidden @ X37 @ ( k1_relat_1 @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t18_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_2 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 ) ) @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('25',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ( r2_hidden @ ( sk_B_1 @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('26',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('29',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_tarski @ ( sk_B_1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X19: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X19 ) ) ),
    inference(demod,[status(thm)],['6','9','10'])).

thf('31',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 ) ) @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','31'])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('33',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('36',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('40',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('41',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['34','40'])).

thf('42',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 ) ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('44',plain,
    ( ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X19: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X19 ) ) ),
    inference(demod,[status(thm)],['6','9','10'])).

thf('46',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EjFLYbsFwe
% 0.12/0.36  % Computer   : n013.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 17:17:55 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.37  % Number of cores: 8
% 0.12/0.37  % Python version: Python 3.6.8
% 0.12/0.37  % Running in FO mode
% 0.35/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.59  % Solved by: fo/fo7.sh
% 0.35/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.59  % done 269 iterations in 0.114s
% 0.35/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.59  % SZS output start Refutation
% 0.35/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.59  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.35/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.59  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.35/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.59  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.35/0.59  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.35/0.59  thf(d5_relat_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.35/0.59       ( ![C:$i]:
% 0.35/0.59         ( ( r2_hidden @ C @ B ) <=>
% 0.35/0.59           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.35/0.59  thf('0', plain,
% 0.35/0.59      (![X31 : $i, X34 : $i]:
% 0.35/0.59         (((X34) = (k2_relat_1 @ X31))
% 0.35/0.59          | (r2_hidden @ 
% 0.35/0.59             (k4_tarski @ (sk_D_1 @ X34 @ X31) @ (sk_C_1 @ X34 @ X31)) @ X31)
% 0.35/0.59          | (r2_hidden @ (sk_C_1 @ X34 @ X31) @ X34))),
% 0.35/0.59      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.35/0.59  thf(l1_zfmisc_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.35/0.59  thf('1', plain,
% 0.35/0.59      (![X16 : $i, X18 : $i]:
% 0.35/0.59         ((r1_tarski @ (k1_tarski @ X16) @ X18) | ~ (r2_hidden @ X16 @ X18))),
% 0.35/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.35/0.59  thf('2', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.35/0.59          | ((X1) = (k2_relat_1 @ X0))
% 0.35/0.59          | (r1_tarski @ 
% 0.35/0.59             (k1_tarski @ (k4_tarski @ (sk_D_1 @ X1 @ X0) @ (sk_C_1 @ X1 @ X0))) @ 
% 0.35/0.59             X0))),
% 0.35/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.59  thf(t3_xboole_1, axiom,
% 0.35/0.59    (![A:$i]:
% 0.35/0.59     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.35/0.59  thf('3', plain,
% 0.35/0.59      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.35/0.59      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.35/0.59  thf('4', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.35/0.59          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.35/0.59          | ((k1_tarski @ 
% 0.35/0.59              (k4_tarski @ (sk_D_1 @ X0 @ k1_xboole_0) @ 
% 0.35/0.59               (sk_C_1 @ X0 @ k1_xboole_0)))
% 0.35/0.59              = (k1_xboole_0)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.59  thf(t20_zfmisc_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.35/0.59         ( k1_tarski @ A ) ) <=>
% 0.35/0.59       ( ( A ) != ( B ) ) ))).
% 0.35/0.59  thf('5', plain,
% 0.35/0.59      (![X19 : $i, X20 : $i]:
% 0.35/0.59         (((X20) != (X19))
% 0.35/0.59          | ((k4_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X19))
% 0.35/0.59              != (k1_tarski @ X20)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.35/0.59  thf('6', plain,
% 0.35/0.59      (![X19 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X19))
% 0.35/0.59           != (k1_tarski @ X19))),
% 0.35/0.59      inference('simplify', [status(thm)], ['5'])).
% 0.35/0.59  thf(idempotence_k3_xboole_0, axiom,
% 0.35/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.35/0.59  thf('7', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.35/0.59      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.35/0.59  thf(t100_xboole_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.59  thf('8', plain,
% 0.35/0.59      (![X2 : $i, X3 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X2 @ X3)
% 0.35/0.59           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.59  thf('9', plain,
% 0.35/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.59      inference('sup+', [status(thm)], ['7', '8'])).
% 0.35/0.59  thf(t92_xboole_1, axiom,
% 0.35/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.59  thf('10', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.35/0.59      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.59  thf('11', plain, (![X19 : $i]: ((k1_xboole_0) != (k1_tarski @ X19))),
% 0.35/0.59      inference('demod', [status(thm)], ['6', '9', '10'])).
% 0.35/0.59  thf('12', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.35/0.59          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.35/0.59      inference('clc', [status(thm)], ['4', '11'])).
% 0.35/0.59  thf('13', plain,
% 0.35/0.59      (![X16 : $i, X18 : $i]:
% 0.35/0.59         ((r1_tarski @ (k1_tarski @ X16) @ X18) | ~ (r2_hidden @ X16 @ X18))),
% 0.35/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.35/0.59  thf('14', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.35/0.59          | (r1_tarski @ (k1_tarski @ (sk_C_1 @ X0 @ k1_xboole_0)) @ X0))),
% 0.35/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.59  thf('15', plain,
% 0.35/0.59      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.35/0.59      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.35/0.59  thf('16', plain,
% 0.35/0.59      ((((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.35/0.59        | ((k1_tarski @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.59  thf('17', plain, (![X19 : $i]: ((k1_xboole_0) != (k1_tarski @ X19))),
% 0.35/0.59      inference('demod', [status(thm)], ['6', '9', '10'])).
% 0.35/0.59  thf('18', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.35/0.59      inference('clc', [status(thm)], ['16', '17'])).
% 0.35/0.59  thf(t7_xboole_0, axiom,
% 0.35/0.59    (![A:$i]:
% 0.35/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.59          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.35/0.59  thf('19', plain,
% 0.35/0.59      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.35/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.35/0.59  thf(t18_relat_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( v1_relat_1 @ B ) =>
% 0.35/0.59       ( ~( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) & 
% 0.35/0.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.35/0.59  thf('20', plain,
% 0.35/0.59      (![X36 : $i, X37 : $i]:
% 0.35/0.59         ((r2_hidden @ (sk_C_2 @ X36) @ (k2_relat_1 @ X36))
% 0.35/0.59          | ~ (r2_hidden @ X37 @ (k1_relat_1 @ X36))
% 0.35/0.59          | ~ (v1_relat_1 @ X36))),
% 0.35/0.59      inference('cnf', [status(esa)], [t18_relat_1])).
% 0.35/0.59  thf('21', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.35/0.59          | ~ (v1_relat_1 @ X0)
% 0.35/0.59          | (r2_hidden @ (sk_C_2 @ X0) @ (k2_relat_1 @ X0)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.59  thf('22', plain,
% 0.35/0.59      (![X16 : $i, X18 : $i]:
% 0.35/0.59         ((r1_tarski @ (k1_tarski @ X16) @ X18) | ~ (r2_hidden @ X16 @ X18))),
% 0.35/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.35/0.59  thf('23', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (~ (v1_relat_1 @ X0)
% 0.35/0.59          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.35/0.59          | (r1_tarski @ (k1_tarski @ (sk_C_2 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.59  thf('24', plain,
% 0.35/0.59      (((r1_tarski @ (k1_tarski @ (sk_C_2 @ k1_xboole_0)) @ k1_xboole_0)
% 0.35/0.59        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.35/0.59        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.35/0.59      inference('sup+', [status(thm)], ['18', '23'])).
% 0.35/0.59  thf(d1_relat_1, axiom,
% 0.35/0.59    (![A:$i]:
% 0.35/0.59     ( ( v1_relat_1 @ A ) <=>
% 0.35/0.59       ( ![B:$i]:
% 0.35/0.59         ( ~( ( r2_hidden @ B @ A ) & 
% 0.35/0.59              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.35/0.59  thf('25', plain,
% 0.35/0.59      (![X26 : $i]: ((v1_relat_1 @ X26) | (r2_hidden @ (sk_B_1 @ X26) @ X26))),
% 0.35/0.59      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.35/0.59  thf('26', plain,
% 0.35/0.59      (![X16 : $i, X18 : $i]:
% 0.35/0.59         ((r1_tarski @ (k1_tarski @ X16) @ X18) | ~ (r2_hidden @ X16 @ X18))),
% 0.35/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.35/0.59  thf('27', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         ((v1_relat_1 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B_1 @ X0)) @ X0))),
% 0.35/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.59  thf('28', plain,
% 0.35/0.59      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.35/0.59      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.35/0.59  thf('29', plain,
% 0.35/0.59      (((v1_relat_1 @ k1_xboole_0)
% 0.35/0.59        | ((k1_tarski @ (sk_B_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.59  thf('30', plain, (![X19 : $i]: ((k1_xboole_0) != (k1_tarski @ X19))),
% 0.35/0.59      inference('demod', [status(thm)], ['6', '9', '10'])).
% 0.35/0.59  thf('31', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.35/0.59      inference('clc', [status(thm)], ['29', '30'])).
% 0.35/0.59  thf('32', plain,
% 0.35/0.59      (((r1_tarski @ (k1_tarski @ (sk_C_2 @ k1_xboole_0)) @ k1_xboole_0)
% 0.35/0.59        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.35/0.59      inference('demod', [status(thm)], ['24', '31'])).
% 0.35/0.59  thf(t60_relat_1, conjecture,
% 0.35/0.59    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.35/0.59     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.35/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.59    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.35/0.59        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.35/0.59    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.35/0.59  thf('33', plain,
% 0.35/0.59      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.35/0.59        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('34', plain,
% 0.35/0.59      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.35/0.59         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.35/0.59      inference('split', [status(esa)], ['33'])).
% 0.35/0.59  thf('35', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.35/0.59      inference('clc', [status(thm)], ['16', '17'])).
% 0.35/0.59  thf('36', plain,
% 0.35/0.59      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.35/0.59         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.35/0.59      inference('split', [status(esa)], ['33'])).
% 0.35/0.59  thf('37', plain,
% 0.35/0.59      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.35/0.59         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.35/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.59  thf('38', plain, ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.35/0.59      inference('simplify', [status(thm)], ['37'])).
% 0.35/0.59  thf('39', plain,
% 0.35/0.59      (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.35/0.59       ~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.35/0.59      inference('split', [status(esa)], ['33'])).
% 0.35/0.59  thf('40', plain, (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.35/0.59      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 0.35/0.59  thf('41', plain, (((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.35/0.59      inference('simpl_trail', [status(thm)], ['34', '40'])).
% 0.35/0.59  thf('42', plain,
% 0.35/0.59      ((r1_tarski @ (k1_tarski @ (sk_C_2 @ k1_xboole_0)) @ k1_xboole_0)),
% 0.35/0.59      inference('simplify_reflect-', [status(thm)], ['32', '41'])).
% 0.35/0.59  thf('43', plain,
% 0.35/0.59      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.35/0.59      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.35/0.59  thf('44', plain, (((k1_tarski @ (sk_C_2 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.35/0.59      inference('sup-', [status(thm)], ['42', '43'])).
% 0.35/0.59  thf('45', plain, (![X19 : $i]: ((k1_xboole_0) != (k1_tarski @ X19))),
% 0.35/0.59      inference('demod', [status(thm)], ['6', '9', '10'])).
% 0.35/0.59  thf('46', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.35/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.35/0.59  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 0.35/0.59  
% 0.35/0.59  % SZS output end Refutation
% 0.35/0.59  
% 0.35/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
