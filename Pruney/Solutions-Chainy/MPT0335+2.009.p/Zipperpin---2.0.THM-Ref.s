%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rkQllwnHDs

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:13 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 313 expanded)
%              Number of leaves         :   22 ( 103 expanded)
%              Depth                    :   20
%              Number of atoms          : 1038 (2624 expanded)
%              Number of equality atoms :  100 ( 254 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) )
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('20',plain,(
    ! [X35: $i,X37: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X35 ) @ X37 )
        = ( k1_tarski @ X35 ) )
      | ( r2_hidden @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_D_1 ) )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('36',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ sk_D_1 ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('44',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('45',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('52',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['37','53'])).

thf('55',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('56',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('57',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X35 ) @ X36 )
       != ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('64',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['36','63'])).

thf('65',plain,(
    ! [X35: $i,X37: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X35 ) @ X37 )
        = ( k1_tarski @ X35 ) )
      | ( r2_hidden @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('66',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_D_1 ) )
    | ( r2_hidden @ sk_D_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) )
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('68',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('69',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('75',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ sk_D_1 ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('77',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X35 ) @ X36 )
       != ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('79',plain,
    ( ( k1_xboole_0
     != ( k1_tarski @ sk_D_1 ) )
    | ~ ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    r2_hidden @ sk_D_1 @ sk_B ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    k1_xboole_0
 != ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('86',plain,(
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['66','85'])).

thf('87',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('88',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('90',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_D_1 @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','91'])).

thf('93',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['86','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('97',plain,(
    r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('99',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('108',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ X0 ) )
      | ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D_1 @ ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','110'])).

thf('112',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('114',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['19','114'])).

thf('116',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_1 )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('118',plain,(
    ( k3_xboole_0 @ sk_C_1 @ sk_A )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['115','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rkQllwnHDs
% 0.17/0.38  % Computer   : n022.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 10:51:11 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 1.93/2.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.93/2.11  % Solved by: fo/fo7.sh
% 1.93/2.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.93/2.11  % done 3123 iterations in 1.620s
% 1.93/2.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.93/2.11  % SZS output start Refutation
% 1.93/2.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.93/2.11  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.93/2.11  thf(sk_A_type, type, sk_A: $i).
% 1.93/2.11  thf(sk_B_type, type, sk_B: $i).
% 1.93/2.11  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.93/2.11  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.93/2.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.93/2.11  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.93/2.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.93/2.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.93/2.11  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.93/2.11  thf(t148_zfmisc_1, conjecture,
% 1.93/2.11    (![A:$i,B:$i,C:$i,D:$i]:
% 1.93/2.11     ( ( ( r1_tarski @ A @ B ) & 
% 1.93/2.11         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.93/2.11         ( r2_hidden @ D @ A ) ) =>
% 1.93/2.11       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 1.93/2.11  thf(zf_stmt_0, negated_conjecture,
% 1.93/2.11    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.93/2.11        ( ( ( r1_tarski @ A @ B ) & 
% 1.93/2.11            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.93/2.11            ( r2_hidden @ D @ A ) ) =>
% 1.93/2.11          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 1.93/2.11    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 1.93/2.11  thf('0', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf(t47_xboole_1, axiom,
% 1.93/2.11    (![A:$i,B:$i]:
% 1.93/2.11     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.93/2.11  thf('1', plain,
% 1.93/2.11      (![X18 : $i, X19 : $i]:
% 1.93/2.11         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 1.93/2.11           = (k4_xboole_0 @ X18 @ X19))),
% 1.93/2.11      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.93/2.11  thf('2', plain,
% 1.93/2.11      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1))
% 1.93/2.11         = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 1.93/2.11      inference('sup+', [status(thm)], ['0', '1'])).
% 1.93/2.11  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf(t28_xboole_1, axiom,
% 1.93/2.11    (![A:$i,B:$i]:
% 1.93/2.11     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.93/2.11  thf('4', plain,
% 1.93/2.11      (![X15 : $i, X16 : $i]:
% 1.93/2.11         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 1.93/2.11      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.93/2.11  thf('5', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 1.93/2.11      inference('sup-', [status(thm)], ['3', '4'])).
% 1.93/2.11  thf(commutativity_k3_xboole_0, axiom,
% 1.93/2.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.93/2.11  thf('6', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.93/2.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.93/2.11  thf('7', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 1.93/2.11      inference('demod', [status(thm)], ['5', '6'])).
% 1.93/2.11  thf('8', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.93/2.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.93/2.11  thf(t49_xboole_1, axiom,
% 1.93/2.11    (![A:$i,B:$i,C:$i]:
% 1.93/2.11     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.93/2.11       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.93/2.11  thf('9', plain,
% 1.93/2.11      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.93/2.11         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 1.93/2.11           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 1.93/2.11      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.93/2.11  thf('10', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.11         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 1.93/2.11           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 1.93/2.11      inference('sup+', [status(thm)], ['8', '9'])).
% 1.93/2.11  thf('11', plain,
% 1.93/2.11      (![X0 : $i]:
% 1.93/2.11         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 1.93/2.11           = (k4_xboole_0 @ sk_A @ X0))),
% 1.93/2.11      inference('sup+', [status(thm)], ['7', '10'])).
% 1.93/2.11  thf('12', plain,
% 1.93/2.11      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))
% 1.93/2.11         = (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 1.93/2.11      inference('sup+', [status(thm)], ['2', '11'])).
% 1.93/2.11  thf('13', plain,
% 1.93/2.11      (![X0 : $i]:
% 1.93/2.11         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 1.93/2.11           = (k4_xboole_0 @ sk_A @ X0))),
% 1.93/2.11      inference('sup+', [status(thm)], ['7', '10'])).
% 1.93/2.11  thf('14', plain,
% 1.93/2.11      (((k4_xboole_0 @ sk_A @ sk_C_1)
% 1.93/2.11         = (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 1.93/2.11      inference('demod', [status(thm)], ['12', '13'])).
% 1.93/2.11  thf(t48_xboole_1, axiom,
% 1.93/2.11    (![A:$i,B:$i]:
% 1.93/2.11     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.93/2.11  thf('15', plain,
% 1.93/2.11      (![X20 : $i, X21 : $i]:
% 1.93/2.11         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.93/2.11           = (k3_xboole_0 @ X20 @ X21))),
% 1.93/2.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.93/2.11  thf('16', plain,
% 1.93/2.11      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C_1))
% 1.93/2.11         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 1.93/2.11      inference('sup+', [status(thm)], ['14', '15'])).
% 1.93/2.11  thf('17', plain,
% 1.93/2.11      (![X20 : $i, X21 : $i]:
% 1.93/2.11         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.93/2.11           = (k3_xboole_0 @ X20 @ X21))),
% 1.93/2.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.93/2.11  thf('18', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.93/2.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.93/2.11  thf('19', plain,
% 1.93/2.11      (((k3_xboole_0 @ sk_C_1 @ sk_A)
% 1.93/2.11         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 1.93/2.11      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.93/2.11  thf(l33_zfmisc_1, axiom,
% 1.93/2.11    (![A:$i,B:$i]:
% 1.93/2.11     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 1.93/2.11       ( ~( r2_hidden @ A @ B ) ) ))).
% 1.93/2.11  thf('20', plain,
% 1.93/2.11      (![X35 : $i, X37 : $i]:
% 1.93/2.11         (((k4_xboole_0 @ (k1_tarski @ X35) @ X37) = (k1_tarski @ X35))
% 1.93/2.11          | (r2_hidden @ X35 @ X37))),
% 1.93/2.11      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 1.93/2.11  thf('21', plain,
% 1.93/2.11      (![X20 : $i, X21 : $i]:
% 1.93/2.11         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.93/2.11           = (k3_xboole_0 @ X20 @ X21))),
% 1.93/2.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.93/2.11  thf('22', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i]:
% 1.93/2.11         (((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.93/2.11          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.93/2.11      inference('sup+', [status(thm)], ['20', '21'])).
% 1.93/2.11  thf('23', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('24', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.93/2.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.93/2.11  thf('25', plain,
% 1.93/2.11      (![X18 : $i, X19 : $i]:
% 1.93/2.11         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 1.93/2.11           = (k4_xboole_0 @ X18 @ X19))),
% 1.93/2.11      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.93/2.11  thf('26', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i]:
% 1.93/2.11         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.93/2.11           = (k4_xboole_0 @ X0 @ X1))),
% 1.93/2.11      inference('sup+', [status(thm)], ['24', '25'])).
% 1.93/2.11  thf('27', plain,
% 1.93/2.11      (((k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_D_1))
% 1.93/2.11         = (k4_xboole_0 @ sk_C_1 @ sk_B))),
% 1.93/2.11      inference('sup+', [status(thm)], ['23', '26'])).
% 1.93/2.11  thf('28', plain,
% 1.93/2.11      (![X20 : $i, X21 : $i]:
% 1.93/2.11         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.93/2.11           = (k3_xboole_0 @ X20 @ X21))),
% 1.93/2.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.93/2.11  thf('29', plain,
% 1.93/2.11      (((k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_C_1 @ sk_B))
% 1.93/2.11         = (k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_D_1)))),
% 1.93/2.11      inference('sup+', [status(thm)], ['27', '28'])).
% 1.93/2.11  thf('30', plain,
% 1.93/2.11      (![X20 : $i, X21 : $i]:
% 1.93/2.11         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.93/2.11           = (k3_xboole_0 @ X20 @ X21))),
% 1.93/2.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.93/2.11  thf('31', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.93/2.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.93/2.11  thf('32', plain,
% 1.93/2.11      (((k3_xboole_0 @ sk_B @ sk_C_1)
% 1.93/2.11         = (k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_D_1)))),
% 1.93/2.11      inference('demod', [status(thm)], ['29', '30', '31'])).
% 1.93/2.11  thf('33', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('34', plain,
% 1.93/2.11      (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_D_1)))),
% 1.93/2.11      inference('demod', [status(thm)], ['32', '33'])).
% 1.93/2.11  thf('35', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i]:
% 1.93/2.11         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.93/2.11           = (k4_xboole_0 @ X0 @ X1))),
% 1.93/2.11      inference('sup+', [status(thm)], ['24', '25'])).
% 1.93/2.11  thf('36', plain,
% 1.93/2.11      (((k4_xboole_0 @ (k1_tarski @ sk_D_1) @ (k1_tarski @ sk_D_1))
% 1.93/2.11         = (k4_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_C_1))),
% 1.93/2.11      inference('sup+', [status(thm)], ['34', '35'])).
% 1.93/2.11  thf(d3_tarski, axiom,
% 1.93/2.11    (![A:$i,B:$i]:
% 1.93/2.11     ( ( r1_tarski @ A @ B ) <=>
% 1.93/2.11       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.93/2.11  thf('37', plain,
% 1.93/2.11      (![X3 : $i, X5 : $i]:
% 1.93/2.11         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.93/2.11      inference('cnf', [status(esa)], [d3_tarski])).
% 1.93/2.11  thf(d10_xboole_0, axiom,
% 1.93/2.11    (![A:$i,B:$i]:
% 1.93/2.11     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.93/2.11  thf('38', plain,
% 1.93/2.11      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 1.93/2.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.93/2.11  thf('39', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 1.93/2.11      inference('simplify', [status(thm)], ['38'])).
% 1.93/2.11  thf('40', plain,
% 1.93/2.11      (![X15 : $i, X16 : $i]:
% 1.93/2.11         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 1.93/2.11      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.93/2.11  thf('41', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.93/2.11      inference('sup-', [status(thm)], ['39', '40'])).
% 1.93/2.11  thf('42', plain,
% 1.93/2.11      (![X18 : $i, X19 : $i]:
% 1.93/2.11         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 1.93/2.11           = (k4_xboole_0 @ X18 @ X19))),
% 1.93/2.11      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.93/2.11  thf('43', plain,
% 1.93/2.11      (![X18 : $i, X19 : $i]:
% 1.93/2.11         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 1.93/2.11           = (k4_xboole_0 @ X18 @ X19))),
% 1.93/2.11      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.93/2.11  thf(d5_xboole_0, axiom,
% 1.93/2.11    (![A:$i,B:$i,C:$i]:
% 1.93/2.11     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.93/2.11       ( ![D:$i]:
% 1.93/2.11         ( ( r2_hidden @ D @ C ) <=>
% 1.93/2.11           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.93/2.11  thf('44', plain,
% 1.93/2.11      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.93/2.11         (~ (r2_hidden @ X10 @ X9)
% 1.93/2.11          | ~ (r2_hidden @ X10 @ X8)
% 1.93/2.12          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 1.93/2.12      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.93/2.12  thf('45', plain,
% 1.93/2.12      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.93/2.12         (~ (r2_hidden @ X10 @ X8)
% 1.93/2.12          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.93/2.12      inference('simplify', [status(thm)], ['44'])).
% 1.93/2.12  thf('46', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.12         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 1.93/2.12          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.93/2.12      inference('sup-', [status(thm)], ['43', '45'])).
% 1.93/2.12  thf('47', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.12         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 1.93/2.12          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.93/2.12      inference('sup-', [status(thm)], ['42', '46'])).
% 1.93/2.12  thf('48', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i]:
% 1.93/2.12         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ X0))
% 1.93/2.12          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.93/2.12      inference('sup-', [status(thm)], ['41', '47'])).
% 1.93/2.12  thf('49', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.93/2.12      inference('sup-', [status(thm)], ['39', '40'])).
% 1.93/2.12  thf('50', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i]:
% 1.93/2.12         (~ (r2_hidden @ X1 @ X0)
% 1.93/2.12          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.93/2.12      inference('demod', [status(thm)], ['48', '49'])).
% 1.93/2.12  thf('51', plain,
% 1.93/2.12      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.93/2.12         (~ (r2_hidden @ X10 @ X9)
% 1.93/2.12          | (r2_hidden @ X10 @ X7)
% 1.93/2.12          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 1.93/2.12      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.93/2.12  thf('52', plain,
% 1.93/2.12      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.93/2.12         ((r2_hidden @ X10 @ X7)
% 1.93/2.12          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.93/2.12      inference('simplify', [status(thm)], ['51'])).
% 1.93/2.12  thf('53', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 1.93/2.12      inference('clc', [status(thm)], ['50', '52'])).
% 1.93/2.12  thf('54', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 1.93/2.12      inference('sup-', [status(thm)], ['37', '53'])).
% 1.93/2.12  thf('55', plain,
% 1.93/2.12      (![X3 : $i, X5 : $i]:
% 1.93/2.12         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.93/2.12      inference('cnf', [status(esa)], [d3_tarski])).
% 1.93/2.12  thf(t3_boole, axiom,
% 1.93/2.12    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.93/2.12  thf('56', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.93/2.12      inference('cnf', [status(esa)], [t3_boole])).
% 1.93/2.12  thf('57', plain,
% 1.93/2.12      (![X35 : $i, X36 : $i]:
% 1.93/2.12         (~ (r2_hidden @ X35 @ X36)
% 1.93/2.12          | ((k4_xboole_0 @ (k1_tarski @ X35) @ X36) != (k1_tarski @ X35)))),
% 1.93/2.12      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 1.93/2.12  thf('58', plain,
% 1.93/2.12      (![X0 : $i]:
% 1.93/2.12         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 1.93/2.12          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 1.93/2.12      inference('sup-', [status(thm)], ['56', '57'])).
% 1.93/2.12  thf('59', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.93/2.12      inference('simplify', [status(thm)], ['58'])).
% 1.93/2.12  thf('60', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.93/2.12      inference('sup-', [status(thm)], ['55', '59'])).
% 1.93/2.12  thf('61', plain,
% 1.93/2.12      (![X12 : $i, X14 : $i]:
% 1.93/2.12         (((X12) = (X14))
% 1.93/2.12          | ~ (r1_tarski @ X14 @ X12)
% 1.93/2.12          | ~ (r1_tarski @ X12 @ X14))),
% 1.93/2.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.93/2.12  thf('62', plain,
% 1.93/2.12      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.93/2.12      inference('sup-', [status(thm)], ['60', '61'])).
% 1.93/2.12  thf('63', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.93/2.12      inference('sup-', [status(thm)], ['54', '62'])).
% 1.93/2.12  thf('64', plain,
% 1.93/2.12      (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_C_1))),
% 1.93/2.12      inference('demod', [status(thm)], ['36', '63'])).
% 1.93/2.12  thf('65', plain,
% 1.93/2.12      (![X35 : $i, X37 : $i]:
% 1.93/2.12         (((k4_xboole_0 @ (k1_tarski @ X35) @ X37) = (k1_tarski @ X35))
% 1.93/2.12          | (r2_hidden @ X35 @ X37))),
% 1.93/2.12      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 1.93/2.12  thf('66', plain,
% 1.93/2.12      ((((k1_xboole_0) = (k1_tarski @ sk_D_1)) | (r2_hidden @ sk_D_1 @ sk_C_1))),
% 1.93/2.12      inference('sup+', [status(thm)], ['64', '65'])).
% 1.93/2.12  thf('67', plain,
% 1.93/2.12      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1))
% 1.93/2.12         = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 1.93/2.12      inference('sup+', [status(thm)], ['0', '1'])).
% 1.93/2.12  thf('68', plain,
% 1.93/2.12      (![X20 : $i, X21 : $i]:
% 1.93/2.12         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.93/2.12           = (k3_xboole_0 @ X20 @ X21))),
% 1.93/2.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.93/2.12  thf('69', plain,
% 1.93/2.12      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1))
% 1.93/2.12         = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1)))),
% 1.93/2.12      inference('sup+', [status(thm)], ['67', '68'])).
% 1.93/2.12  thf('70', plain,
% 1.93/2.12      (![X20 : $i, X21 : $i]:
% 1.93/2.12         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.93/2.12           = (k3_xboole_0 @ X20 @ X21))),
% 1.93/2.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.93/2.12  thf('71', plain,
% 1.93/2.12      (((k3_xboole_0 @ sk_B @ sk_C_1)
% 1.93/2.12         = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1)))),
% 1.93/2.12      inference('demod', [status(thm)], ['69', '70'])).
% 1.93/2.12  thf('72', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('73', plain,
% 1.93/2.12      (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1)))),
% 1.93/2.12      inference('demod', [status(thm)], ['71', '72'])).
% 1.93/2.12  thf('74', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i]:
% 1.93/2.12         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.93/2.12           = (k4_xboole_0 @ X0 @ X1))),
% 1.93/2.12      inference('sup+', [status(thm)], ['24', '25'])).
% 1.93/2.12  thf('75', plain,
% 1.93/2.12      (((k4_xboole_0 @ (k1_tarski @ sk_D_1) @ (k1_tarski @ sk_D_1))
% 1.93/2.12         = (k4_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_B))),
% 1.93/2.12      inference('sup+', [status(thm)], ['73', '74'])).
% 1.93/2.12  thf('76', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.93/2.12      inference('sup-', [status(thm)], ['54', '62'])).
% 1.93/2.12  thf('77', plain,
% 1.93/2.12      (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_B))),
% 1.93/2.12      inference('demod', [status(thm)], ['75', '76'])).
% 1.93/2.12  thf('78', plain,
% 1.93/2.12      (![X35 : $i, X36 : $i]:
% 1.93/2.12         (~ (r2_hidden @ X35 @ X36)
% 1.93/2.12          | ((k4_xboole_0 @ (k1_tarski @ X35) @ X36) != (k1_tarski @ X35)))),
% 1.93/2.12      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 1.93/2.12  thf('79', plain,
% 1.93/2.12      ((((k1_xboole_0) != (k1_tarski @ sk_D_1)) | ~ (r2_hidden @ sk_D_1 @ sk_B))),
% 1.93/2.12      inference('sup-', [status(thm)], ['77', '78'])).
% 1.93/2.12  thf('80', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('81', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('82', plain,
% 1.93/2.12      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.93/2.12         (~ (r2_hidden @ X2 @ X3)
% 1.93/2.12          | (r2_hidden @ X2 @ X4)
% 1.93/2.12          | ~ (r1_tarski @ X3 @ X4))),
% 1.93/2.12      inference('cnf', [status(esa)], [d3_tarski])).
% 1.93/2.12  thf('83', plain,
% 1.93/2.12      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 1.93/2.12      inference('sup-', [status(thm)], ['81', '82'])).
% 1.93/2.12  thf('84', plain, ((r2_hidden @ sk_D_1 @ sk_B)),
% 1.93/2.12      inference('sup-', [status(thm)], ['80', '83'])).
% 1.93/2.12  thf('85', plain, (((k1_xboole_0) != (k1_tarski @ sk_D_1))),
% 1.93/2.12      inference('demod', [status(thm)], ['79', '84'])).
% 1.93/2.12  thf('86', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 1.93/2.12      inference('simplify_reflect-', [status(thm)], ['66', '85'])).
% 1.93/2.12  thf('87', plain,
% 1.93/2.12      (![X18 : $i, X19 : $i]:
% 1.93/2.12         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 1.93/2.12           = (k4_xboole_0 @ X18 @ X19))),
% 1.93/2.12      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.93/2.12  thf('88', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('89', plain,
% 1.93/2.12      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.93/2.12         (~ (r2_hidden @ X6 @ X7)
% 1.93/2.12          | (r2_hidden @ X6 @ X8)
% 1.93/2.12          | (r2_hidden @ X6 @ X9)
% 1.93/2.12          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 1.93/2.12      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.93/2.12  thf('90', plain,
% 1.93/2.12      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.93/2.12         ((r2_hidden @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 1.93/2.12          | (r2_hidden @ X6 @ X8)
% 1.93/2.12          | ~ (r2_hidden @ X6 @ X7))),
% 1.93/2.12      inference('simplify', [status(thm)], ['89'])).
% 1.93/2.12  thf('91', plain,
% 1.93/2.12      (![X0 : $i]:
% 1.93/2.12         ((r2_hidden @ sk_D_1 @ X0)
% 1.93/2.12          | (r2_hidden @ sk_D_1 @ (k4_xboole_0 @ sk_A @ X0)))),
% 1.93/2.12      inference('sup-', [status(thm)], ['88', '90'])).
% 1.93/2.12  thf('92', plain,
% 1.93/2.12      (![X0 : $i]:
% 1.93/2.12         ((r2_hidden @ sk_D_1 @ (k4_xboole_0 @ sk_A @ X0))
% 1.93/2.12          | (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_A @ X0)))),
% 1.93/2.12      inference('sup+', [status(thm)], ['87', '91'])).
% 1.93/2.12  thf('93', plain,
% 1.93/2.12      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.93/2.12         (~ (r2_hidden @ X10 @ X8)
% 1.93/2.12          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.93/2.12      inference('simplify', [status(thm)], ['44'])).
% 1.93/2.12  thf('94', plain,
% 1.93/2.12      (![X0 : $i]:
% 1.93/2.12         ((r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_A @ X0))
% 1.93/2.12          | ~ (r2_hidden @ sk_D_1 @ X0))),
% 1.93/2.12      inference('sup-', [status(thm)], ['92', '93'])).
% 1.93/2.12  thf('95', plain, ((r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_A @ sk_C_1))),
% 1.93/2.12      inference('sup-', [status(thm)], ['86', '94'])).
% 1.93/2.12  thf('96', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.93/2.12      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.93/2.12  thf('97', plain, ((r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.93/2.12      inference('demod', [status(thm)], ['95', '96'])).
% 1.93/2.12  thf('98', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.93/2.12      inference('sup-', [status(thm)], ['54', '62'])).
% 1.93/2.12  thf('99', plain,
% 1.93/2.12      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.93/2.12         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 1.93/2.12           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 1.93/2.12      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.93/2.12  thf('100', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i]:
% 1.93/2.12         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.93/2.12           = (k1_xboole_0))),
% 1.93/2.12      inference('sup+', [status(thm)], ['98', '99'])).
% 1.93/2.12  thf('101', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i]:
% 1.93/2.12         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.93/2.12           = (k4_xboole_0 @ X0 @ X1))),
% 1.93/2.12      inference('sup+', [status(thm)], ['24', '25'])).
% 1.93/2.12  thf('102', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i]:
% 1.93/2.12         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.93/2.12      inference('demod', [status(thm)], ['100', '101'])).
% 1.93/2.12  thf('103', plain,
% 1.93/2.12      (![X18 : $i, X19 : $i]:
% 1.93/2.12         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 1.93/2.12           = (k4_xboole_0 @ X18 @ X19))),
% 1.93/2.12      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.93/2.12  thf('104', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i]:
% 1.93/2.12         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 1.93/2.12           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.93/2.12      inference('sup+', [status(thm)], ['102', '103'])).
% 1.93/2.12  thf('105', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.93/2.12      inference('cnf', [status(esa)], [t3_boole])).
% 1.93/2.12  thf('106', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i]:
% 1.93/2.12         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.93/2.12      inference('demod', [status(thm)], ['104', '105'])).
% 1.93/2.12  thf('107', plain,
% 1.93/2.12      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.93/2.12         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 1.93/2.12           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 1.93/2.12      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.93/2.12  thf('108', plain,
% 1.93/2.12      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.93/2.12         (~ (r2_hidden @ X10 @ X8)
% 1.93/2.12          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.93/2.12      inference('simplify', [status(thm)], ['44'])).
% 1.93/2.12  thf('109', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.93/2.12         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 1.93/2.12          | ~ (r2_hidden @ X3 @ X0))),
% 1.93/2.12      inference('sup-', [status(thm)], ['107', '108'])).
% 1.93/2.12  thf('110', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.93/2.12         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ X0))
% 1.93/2.12          | ~ (r2_hidden @ X3 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.93/2.12      inference('sup-', [status(thm)], ['106', '109'])).
% 1.93/2.12  thf('111', plain,
% 1.93/2.12      (![X0 : $i]: ~ (r2_hidden @ sk_D_1 @ (k4_xboole_0 @ X0 @ sk_A))),
% 1.93/2.12      inference('sup-', [status(thm)], ['97', '110'])).
% 1.93/2.12  thf('112', plain,
% 1.93/2.12      (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A))),
% 1.93/2.12      inference('sup-', [status(thm)], ['22', '111'])).
% 1.93/2.12  thf('113', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.93/2.12      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.93/2.12  thf('114', plain,
% 1.93/2.12      (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 1.93/2.12      inference('demod', [status(thm)], ['112', '113'])).
% 1.93/2.12  thf('115', plain, (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.93/2.12      inference('sup+', [status(thm)], ['19', '114'])).
% 1.93/2.12  thf('116', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) != (k1_tarski @ sk_D_1))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('117', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.93/2.12      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.93/2.12  thf('118', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) != (k1_tarski @ sk_D_1))),
% 1.93/2.12      inference('demod', [status(thm)], ['116', '117'])).
% 1.93/2.12  thf('119', plain, ($false),
% 1.93/2.12      inference('simplify_reflect-', [status(thm)], ['115', '118'])).
% 1.93/2.12  
% 1.93/2.12  % SZS output end Refutation
% 1.93/2.12  
% 1.93/2.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
