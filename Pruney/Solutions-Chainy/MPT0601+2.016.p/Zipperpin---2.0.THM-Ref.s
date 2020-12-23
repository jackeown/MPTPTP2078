%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CeSallksdg

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:43 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 134 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  524 (1113 expanded)
%              Number of equality atoms :   42 (  94 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21
        = ( k1_relat_1 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X21 @ X18 ) @ ( sk_D_1 @ X21 @ X18 ) ) @ X18 )
      | ( r2_hidden @ ( sk_C @ X21 @ X18 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X29 ) @ ( k1_relat_1 @ X29 ) )
      | ~ ( r2_hidden @ X30 @ ( k2_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t46_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ X10 )
        = X10 )
      | ~ ( r2_hidden @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_C_1 @ k1_xboole_0 ) ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ X13 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('18',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k11_relat_1 @ X32 @ X33 ) )
      | ( r2_hidden @ ( k4_tarski @ X33 @ X31 ) @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 )
      | ( r2_hidden @ X16 @ X19 )
      | ( X19
       != ( k1_relat_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ ( k1_relat_1 @ X18 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['25'])).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( r2_hidden @ ( k4_tarski @ X20 @ ( sk_D_2 @ X20 @ X18 ) ) @ X18 )
      | ( X19
       != ( k1_relat_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('30',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X20 @ ( sk_D_2 @ X20 @ X18 ) ) @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_2 @ sk_A @ sk_B ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X33 @ X31 ) @ X32 )
      | ( r2_hidden @ X31 @ ( k11_relat_1 @ X32 @ X33 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('33',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ X10 )
        = X10 )
      | ~ ( r2_hidden @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

thf('38',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_D_2 @ sk_A @ sk_B ) ) @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ X13 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('42',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['26','40','41'])).

thf('43',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['24','42'])).

thf('44',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['25'])).

thf('48',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['26','40'])).

thf('49',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CeSallksdg
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:02:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.61/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.83  % Solved by: fo/fo7.sh
% 0.61/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.83  % done 443 iterations in 0.376s
% 0.61/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.83  % SZS output start Refutation
% 0.61/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.83  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.61/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.83  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.61/0.83  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.61/0.83  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.61/0.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.61/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.61/0.83  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.61/0.83  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.61/0.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.83  thf(d4_relat_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.61/0.83       ( ![C:$i]:
% 0.61/0.83         ( ( r2_hidden @ C @ B ) <=>
% 0.61/0.83           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.61/0.83  thf('0', plain,
% 0.61/0.83      (![X18 : $i, X21 : $i]:
% 0.61/0.83         (((X21) = (k1_relat_1 @ X18))
% 0.61/0.83          | (r2_hidden @ 
% 0.61/0.83             (k4_tarski @ (sk_C @ X21 @ X18) @ (sk_D_1 @ X21 @ X18)) @ X18)
% 0.61/0.83          | (r2_hidden @ (sk_C @ X21 @ X18) @ X21))),
% 0.61/0.83      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.61/0.83  thf(t60_relat_1, axiom,
% 0.61/0.83    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.61/0.83     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.61/0.83  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.83      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.61/0.83  thf(t19_relat_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( v1_relat_1 @ B ) =>
% 0.61/0.83       ( ~( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) & 
% 0.61/0.83            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.61/0.83  thf('2', plain,
% 0.61/0.83      (![X29 : $i, X30 : $i]:
% 0.61/0.83         ((r2_hidden @ (sk_C_1 @ X29) @ (k1_relat_1 @ X29))
% 0.61/0.83          | ~ (r2_hidden @ X30 @ (k2_relat_1 @ X29))
% 0.61/0.83          | ~ (v1_relat_1 @ X29))),
% 0.61/0.83      inference('cnf', [status(esa)], [t19_relat_1])).
% 0.61/0.83  thf('3', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.61/0.83          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.61/0.83          | (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ (k1_relat_1 @ k1_xboole_0)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['1', '2'])).
% 0.61/0.83  thf(t205_relat_1, conjecture,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( v1_relat_1 @ B ) =>
% 0.61/0.83       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.61/0.83         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.61/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.83    (~( ![A:$i,B:$i]:
% 0.61/0.83        ( ( v1_relat_1 @ B ) =>
% 0.61/0.83          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.61/0.83            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.61/0.83    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.61/0.83  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(t2_boole, axiom,
% 0.61/0.83    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.61/0.83  thf('5', plain,
% 0.61/0.83      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.83      inference('cnf', [status(esa)], [t2_boole])).
% 0.61/0.83  thf(fc1_relat_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.61/0.83  thf('6', plain,
% 0.61/0.83      (![X23 : $i, X24 : $i]:
% 0.61/0.83         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k3_xboole_0 @ X23 @ X24)))),
% 0.61/0.83      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.61/0.83  thf('7', plain,
% 0.61/0.83      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ X0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['5', '6'])).
% 0.61/0.83  thf('8', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.61/0.83      inference('sup-', [status(thm)], ['4', '7'])).
% 0.61/0.83  thf('9', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.83      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.61/0.83  thf('10', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.61/0.83          | (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0))),
% 0.61/0.83      inference('demod', [status(thm)], ['3', '8', '9'])).
% 0.61/0.83  thf('11', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.61/0.83          | ((X0) = (k1_relat_1 @ k1_xboole_0))
% 0.61/0.83          | (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0))),
% 0.61/0.83      inference('sup-', [status(thm)], ['0', '10'])).
% 0.61/0.83  thf('12', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.83      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.61/0.83  thf('13', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.61/0.83          | ((X0) = (k1_xboole_0))
% 0.61/0.83          | (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0))),
% 0.61/0.83      inference('demod', [status(thm)], ['11', '12'])).
% 0.61/0.83  thf(t46_zfmisc_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( r2_hidden @ A @ B ) =>
% 0.61/0.83       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.61/0.83  thf('14', plain,
% 0.61/0.83      (![X10 : $i, X11 : $i]:
% 0.61/0.83         (((k2_xboole_0 @ (k1_tarski @ X11) @ X10) = (X10))
% 0.61/0.83          | ~ (r2_hidden @ X11 @ X10))),
% 0.61/0.83      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 0.61/0.83  thf('15', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         (((X0) = (k1_xboole_0))
% 0.61/0.83          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.61/0.83          | ((k2_xboole_0 @ (k1_tarski @ (sk_C_1 @ k1_xboole_0)) @ k1_xboole_0)
% 0.61/0.83              = (k1_xboole_0)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['13', '14'])).
% 0.61/0.83  thf(t49_zfmisc_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.61/0.83  thf('16', plain,
% 0.61/0.83      (![X12 : $i, X13 : $i]:
% 0.61/0.83         ((k2_xboole_0 @ (k1_tarski @ X12) @ X13) != (k1_xboole_0))),
% 0.61/0.83      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.61/0.83  thf('17', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.61/0.83      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.61/0.83  thf(t204_relat_1, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i]:
% 0.61/0.83     ( ( v1_relat_1 @ C ) =>
% 0.61/0.83       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.61/0.83         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.61/0.83  thf('18', plain,
% 0.61/0.83      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.61/0.83         (~ (r2_hidden @ X31 @ (k11_relat_1 @ X32 @ X33))
% 0.61/0.83          | (r2_hidden @ (k4_tarski @ X33 @ X31) @ X32)
% 0.61/0.83          | ~ (v1_relat_1 @ X32))),
% 0.61/0.83      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.61/0.83  thf('19', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]:
% 0.61/0.83         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.61/0.83          | ~ (v1_relat_1 @ X1)
% 0.61/0.83          | (r2_hidden @ 
% 0.61/0.83             (k4_tarski @ X0 @ (sk_C @ (k11_relat_1 @ X1 @ X0) @ k1_xboole_0)) @ 
% 0.61/0.83             X1))),
% 0.61/0.83      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.83  thf('20', plain,
% 0.61/0.83      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.61/0.83         (~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X18)
% 0.61/0.83          | (r2_hidden @ X16 @ X19)
% 0.61/0.83          | ((X19) != (k1_relat_1 @ X18)))),
% 0.61/0.83      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.61/0.83  thf('21', plain,
% 0.61/0.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.83         ((r2_hidden @ X16 @ (k1_relat_1 @ X18))
% 0.61/0.83          | ~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X18))),
% 0.61/0.83      inference('simplify', [status(thm)], ['20'])).
% 0.61/0.83  thf('22', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]:
% 0.61/0.83         (~ (v1_relat_1 @ X0)
% 0.61/0.83          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.61/0.83          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['19', '21'])).
% 0.61/0.83  thf('23', plain,
% 0.61/0.83      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.61/0.83        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('24', plain,
% 0.61/0.83      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.61/0.83         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.61/0.83      inference('split', [status(esa)], ['23'])).
% 0.61/0.83  thf('25', plain,
% 0.61/0.83      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.61/0.83        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('26', plain,
% 0.61/0.83      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.61/0.83       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.61/0.83      inference('split', [status(esa)], ['25'])).
% 0.61/0.83  thf('27', plain,
% 0.61/0.83      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.61/0.83         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.61/0.83      inference('split', [status(esa)], ['23'])).
% 0.61/0.83  thf('28', plain,
% 0.61/0.83      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.61/0.83         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.61/0.83      inference('split', [status(esa)], ['25'])).
% 0.61/0.83  thf('29', plain,
% 0.61/0.83      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.61/0.83         (~ (r2_hidden @ X20 @ X19)
% 0.61/0.83          | (r2_hidden @ (k4_tarski @ X20 @ (sk_D_2 @ X20 @ X18)) @ X18)
% 0.61/0.83          | ((X19) != (k1_relat_1 @ X18)))),
% 0.61/0.83      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.61/0.83  thf('30', plain,
% 0.61/0.83      (![X18 : $i, X20 : $i]:
% 0.61/0.83         ((r2_hidden @ (k4_tarski @ X20 @ (sk_D_2 @ X20 @ X18)) @ X18)
% 0.61/0.83          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X18)))),
% 0.61/0.83      inference('simplify', [status(thm)], ['29'])).
% 0.61/0.83  thf('31', plain,
% 0.61/0.83      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_2 @ sk_A @ sk_B)) @ sk_B))
% 0.61/0.83         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.61/0.83      inference('sup-', [status(thm)], ['28', '30'])).
% 0.61/0.83  thf('32', plain,
% 0.61/0.83      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.61/0.83         (~ (r2_hidden @ (k4_tarski @ X33 @ X31) @ X32)
% 0.61/0.83          | (r2_hidden @ X31 @ (k11_relat_1 @ X32 @ X33))
% 0.61/0.83          | ~ (v1_relat_1 @ X32))),
% 0.61/0.83      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.61/0.83  thf('33', plain,
% 0.61/0.83      (((~ (v1_relat_1 @ sk_B)
% 0.61/0.83         | (r2_hidden @ (sk_D_2 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A))))
% 0.61/0.83         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.61/0.83      inference('sup-', [status(thm)], ['31', '32'])).
% 0.61/0.83  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('35', plain,
% 0.61/0.83      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A)))
% 0.61/0.83         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.61/0.83      inference('demod', [status(thm)], ['33', '34'])).
% 0.61/0.83  thf('36', plain,
% 0.61/0.83      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_B) @ k1_xboole_0))
% 0.61/0.83         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.61/0.83             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.61/0.83      inference('sup+', [status(thm)], ['27', '35'])).
% 0.61/0.83  thf('37', plain,
% 0.61/0.83      (![X10 : $i, X11 : $i]:
% 0.61/0.83         (((k2_xboole_0 @ (k1_tarski @ X11) @ X10) = (X10))
% 0.61/0.83          | ~ (r2_hidden @ X11 @ X10))),
% 0.61/0.83      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 0.61/0.83  thf('38', plain,
% 0.61/0.83      ((((k2_xboole_0 @ (k1_tarski @ (sk_D_2 @ sk_A @ sk_B)) @ k1_xboole_0)
% 0.61/0.83          = (k1_xboole_0)))
% 0.61/0.83         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.61/0.83             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.61/0.83      inference('sup-', [status(thm)], ['36', '37'])).
% 0.61/0.83  thf('39', plain,
% 0.61/0.83      (![X12 : $i, X13 : $i]:
% 0.61/0.83         ((k2_xboole_0 @ (k1_tarski @ X12) @ X13) != (k1_xboole_0))),
% 0.61/0.83      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.61/0.83  thf('40', plain,
% 0.61/0.83      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.61/0.83       ~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.61/0.83      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.61/0.83  thf('41', plain,
% 0.61/0.83      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.61/0.83       (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.61/0.83      inference('split', [status(esa)], ['23'])).
% 0.61/0.83  thf('42', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.61/0.83      inference('sat_resolution*', [status(thm)], ['26', '40', '41'])).
% 0.61/0.83  thf('43', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.61/0.83      inference('simpl_trail', [status(thm)], ['24', '42'])).
% 0.61/0.83  thf('44', plain,
% 0.61/0.83      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B))),
% 0.61/0.83      inference('sup-', [status(thm)], ['22', '43'])).
% 0.61/0.83  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('46', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.61/0.83      inference('demod', [status(thm)], ['44', '45'])).
% 0.61/0.83  thf('47', plain,
% 0.61/0.83      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.61/0.83         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.61/0.83      inference('split', [status(esa)], ['25'])).
% 0.61/0.83  thf('48', plain, (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.61/0.83      inference('sat_resolution*', [status(thm)], ['26', '40'])).
% 0.61/0.83  thf('49', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.61/0.83      inference('simpl_trail', [status(thm)], ['47', '48'])).
% 0.61/0.83  thf('50', plain, ($false),
% 0.61/0.83      inference('simplify_reflect-', [status(thm)], ['46', '49'])).
% 0.61/0.83  
% 0.61/0.83  % SZS output end Refutation
% 0.61/0.83  
% 0.61/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
