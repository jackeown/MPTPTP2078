%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DG9jPfIWbH

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:11 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 156 expanded)
%              Number of leaves         :   31 (  59 expanded)
%              Depth                    :   17
%              Number of atoms          :  635 (1164 expanded)
%              Number of equality atoms :   69 ( 125 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 )
      | ( X20 = X21 )
      | ( X20 = X22 )
      | ( X20 = X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','11'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','23'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('26',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B_1 @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B_1 @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X31 @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_tarski @ X31 ) @ ( k2_tarski @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('38',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('41',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_enumset1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k2_tarski @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['26','27','28','41'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( r2_hidden @ X24 @ X28 )
      | ( X28
       != ( k1_enumset1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X24 @ ( k1_enumset1 @ X27 @ X26 @ X25 ) )
      | ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B_1 @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['42','44'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('47',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X25 @ X26 @ X27 )
      | ( X28
       != ( k1_enumset1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X25 @ X26 @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k1_enumset1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_C @ sk_B_1 @ sk_A )
      | ~ ( zip_tseitin_0 @ X0 @ sk_C @ sk_B_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_B_1 )
      | ( X0 = sk_B_1 )
      | ( X0 = sk_C )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_C @ sk_B_1 @ sk_A )
      | ( X0 = sk_C )
      | ( X0 = sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X20 != X19 )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ~ ( zip_tseitin_0 @ X19 @ X21 @ X22 @ X19 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_A = sk_B_1 )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('57',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DG9jPfIWbH
% 0.15/0.38  % Computer   : n019.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 10:45:07 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 115 iterations in 0.067s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.56  thf(d1_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.56     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.56       ( ![E:$i]:
% 0.37/0.56         ( ( r2_hidden @ E @ D ) <=>
% 0.37/0.56           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, axiom,
% 0.37/0.56    (![E:$i,C:$i,B:$i,A:$i]:
% 0.37/0.56     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.37/0.56       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.56         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23)
% 0.37/0.56          | ((X20) = (X21))
% 0.37/0.56          | ((X20) = (X22))
% 0.37/0.56          | ((X20) = (X23)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t25_zfmisc_1, conjecture,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.37/0.56          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_1, negated_conjecture,
% 0.37/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.56        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.37/0.56             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.56  thf(t28_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X14 : $i, X15 : $i]:
% 0.37/0.56         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.37/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C))
% 0.37/0.56         = (k1_tarski @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.56  thf(t100_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X11 @ X12)
% 0.37/0.56           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C))
% 0.37/0.56         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.56  thf(d10_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.56  thf('7', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.37/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X14 : $i, X15 : $i]:
% 0.37/0.56         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.37/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.56  thf('9', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X11 @ X12)
% 0.37/0.56           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['9', '10'])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C))
% 0.37/0.56         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['5', '11'])).
% 0.37/0.56  thf(t7_xboole_0, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['9', '10'])).
% 0.37/0.56  thf(t1_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.37/0.56       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.56         ((r2_hidden @ X3 @ X4)
% 0.37/0.56          | (r2_hidden @ X3 @ X5)
% 0.37/0.56          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.37/0.56          | (r2_hidden @ X1 @ X0)
% 0.37/0.56          | (r2_hidden @ X1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['16'])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['9', '10'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X3 @ X4)
% 0.37/0.56          | ~ (r2_hidden @ X3 @ X5)
% 0.37/0.56          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.37/0.56          | ~ (r2_hidden @ X1 @ X0)
% 0.37/0.56          | ~ (r2_hidden @ X1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X1 @ X0)
% 0.37/0.56          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.37/0.56      inference('clc', [status(thm)], ['17', '21'])).
% 0.37/0.56  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['13', '22'])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C))
% 0.37/0.56         = (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['12', '23'])).
% 0.37/0.56  thf(t98_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i]:
% 0.37/0.56         ((k2_xboole_0 @ X17 @ X18)
% 0.37/0.56           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (((k2_xboole_0 @ (k2_tarski @ sk_B_1 @ sk_C) @ (k1_tarski @ sk_A))
% 0.37/0.56         = (k5_xboole_0 @ (k2_tarski @ sk_B_1 @ sk_C) @ k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['24', '25'])).
% 0.37/0.56  thf(commutativity_k2_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.56  thf(t42_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.37/0.56       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.37/0.56         ((k1_enumset1 @ X31 @ X32 @ X33)
% 0.37/0.56           = (k2_xboole_0 @ (k1_tarski @ X31) @ (k2_tarski @ X32 @ X33)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.37/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.56  thf('29', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (![X14 : $i, X15 : $i]:
% 0.37/0.56         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.37/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X11 @ X12)
% 0.37/0.56           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.56           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['31', '32'])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['9', '10'])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.56           = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['33', '34'])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i]:
% 0.37/0.56         ((k2_xboole_0 @ X17 @ X18)
% 0.37/0.56           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.37/0.56           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['35', '36'])).
% 0.37/0.56  thf(t1_boole, axiom,
% 0.37/0.56    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.56  thf('38', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((X0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.56  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['13', '22'])).
% 0.37/0.56  thf('41', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      (((k1_enumset1 @ sk_A @ sk_B_1 @ sk_C) = (k2_tarski @ sk_B_1 @ sk_C))),
% 0.37/0.56      inference('demod', [status(thm)], ['26', '27', '28', '41'])).
% 0.37/0.56  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.37/0.56  thf(zf_stmt_3, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.56     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.56       ( ![E:$i]:
% 0.37/0.56         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.37/0.56         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.37/0.56          | (r2_hidden @ X24 @ X28)
% 0.37/0.56          | ((X28) != (k1_enumset1 @ X27 @ X26 @ X25)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.56         ((r2_hidden @ X24 @ (k1_enumset1 @ X27 @ X26 @ X25))
% 0.37/0.56          | (zip_tseitin_0 @ X24 @ X25 @ X26 @ X27))),
% 0.37/0.56      inference('simplify', [status(thm)], ['43'])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r2_hidden @ X0 @ (k2_tarski @ sk_B_1 @ sk_C))
% 0.37/0.56          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.56      inference('sup+', [status(thm)], ['42', '44'])).
% 0.37/0.56  thf(t70_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      (![X35 : $i, X36 : $i]:
% 0.37/0.56         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.37/0.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X29 @ X28)
% 0.37/0.56          | ~ (zip_tseitin_0 @ X29 @ X25 @ X26 @ X27)
% 0.37/0.56          | ((X28) != (k1_enumset1 @ X27 @ X26 @ X25)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.56  thf('48', plain,
% 0.37/0.56      (![X25 : $i, X26 : $i, X27 : $i, X29 : $i]:
% 0.37/0.56         (~ (zip_tseitin_0 @ X29 @ X25 @ X26 @ X27)
% 0.37/0.56          | ~ (r2_hidden @ X29 @ (k1_enumset1 @ X27 @ X26 @ X25)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['47'])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.37/0.56          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['46', '48'])).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((zip_tseitin_0 @ X0 @ sk_C @ sk_B_1 @ sk_A)
% 0.37/0.56          | ~ (zip_tseitin_0 @ X0 @ sk_C @ sk_B_1 @ sk_B_1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['45', '49'])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((X0) = (sk_B_1))
% 0.37/0.56          | ((X0) = (sk_B_1))
% 0.37/0.56          | ((X0) = (sk_C))
% 0.37/0.56          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['0', '50'])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((zip_tseitin_0 @ X0 @ sk_C @ sk_B_1 @ sk_A)
% 0.37/0.56          | ((X0) = (sk_C))
% 0.37/0.56          | ((X0) = (sk_B_1)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['51'])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.56         (((X20) != (X19)) | ~ (zip_tseitin_0 @ X20 @ X21 @ X22 @ X19))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.37/0.56         ~ (zip_tseitin_0 @ X19 @ X21 @ X22 @ X19)),
% 0.37/0.56      inference('simplify', [status(thm)], ['53'])).
% 0.37/0.56  thf('55', plain, ((((sk_A) = (sk_B_1)) | ((sk_A) = (sk_C)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['52', '54'])).
% 0.37/0.56  thf('56', plain, (((sk_A) != (sk_C))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.56  thf('57', plain, (((sk_A) != (sk_B_1))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.56  thf('58', plain, ($false),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['55', '56', '57'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.40/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
