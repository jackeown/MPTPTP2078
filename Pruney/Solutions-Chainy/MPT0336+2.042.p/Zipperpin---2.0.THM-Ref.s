%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q3qPRK2Pu8

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:25 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 187 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :   22
%              Number of atoms          :  596 (1515 expanded)
%              Number of equality atoms :   46 ( 104 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k3_xboole_0 @ X8 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('16',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k4_xboole_0 @ X35 @ ( k1_tarski @ X36 ) )
        = X35 )
      | ( r2_hidden @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_xboole_0 @ X25 @ X27 )
      | ( ( k4_xboole_0 @ X25 @ X27 )
       != X25 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) )
    | ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k3_xboole_0 @ X8 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ sk_D_1 @ sk_B )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('41',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) )
    | ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('43',plain,
    ( ( sk_A
      = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) )
    | ( r2_hidden @ sk_D_1 @ sk_B )
    | ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_B )
    | ( sk_A
      = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('47',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
    | ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference(demod,[status(thm)],['33','50'])).

thf('52',plain,(
    ~ ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_xboole_0 @ X25 @ X27 )
      | ( ( k4_xboole_0 @ X25 @ X27 )
       != X25 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('55',plain,
    ( ( sk_A != sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('58',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('59',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','60'])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('63',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q3qPRK2Pu8
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.75/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.93  % Solved by: fo/fo7.sh
% 0.75/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.93  % done 631 iterations in 0.490s
% 0.75/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.93  % SZS output start Refutation
% 0.75/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.93  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/0.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.75/0.93  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.93  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.93  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.93  thf(t149_zfmisc_1, conjecture,
% 0.75/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.93     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.75/0.93         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.75/0.93       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.75/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.93    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.93        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.75/0.93            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.75/0.93          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.75/0.93    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.75/0.93  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(d7_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.75/0.93       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.75/0.93  thf('2', plain,
% 0.75/0.93      (![X8 : $i, X9 : $i]:
% 0.75/0.93         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.75/0.93      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.75/0.93  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.93  thf(commutativity_k3_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.75/0.93  thf('4', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.93  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.75/0.93      inference('demod', [status(thm)], ['3', '4'])).
% 0.75/0.93  thf('6', plain,
% 0.75/0.93      (![X8 : $i, X10 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ X8 @ X10)
% 0.75/0.93          | ((k3_xboole_0 @ X8 @ X10) != (k1_xboole_0)))),
% 0.75/0.93      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.75/0.93  thf('7', plain,
% 0.75/0.93      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['5', '6'])).
% 0.75/0.93  thf('8', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.75/0.93      inference('simplify', [status(thm)], ['7'])).
% 0.75/0.93  thf('9', plain,
% 0.75/0.93      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('10', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.93  thf('11', plain,
% 0.75/0.93      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))),
% 0.75/0.93      inference('demod', [status(thm)], ['9', '10'])).
% 0.75/0.93  thf(t28_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/0.93  thf('12', plain,
% 0.75/0.93      (![X19 : $i, X20 : $i]:
% 0.75/0.93         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.75/0.93      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.93  thf('13', plain,
% 0.75/0.93      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))
% 0.75/0.93         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.75/0.93      inference('sup-', [status(thm)], ['11', '12'])).
% 0.75/0.93  thf('14', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.93  thf('15', plain,
% 0.75/0.93      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.75/0.93         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.75/0.93      inference('demod', [status(thm)], ['13', '14'])).
% 0.75/0.93  thf(t65_zfmisc_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.75/0.93       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.75/0.93  thf('16', plain,
% 0.75/0.93      (![X35 : $i, X36 : $i]:
% 0.75/0.93         (((k4_xboole_0 @ X35 @ (k1_tarski @ X36)) = (X35))
% 0.75/0.93          | (r2_hidden @ X36 @ X35))),
% 0.75/0.93      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.75/0.93  thf(t83_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/0.93  thf('17', plain,
% 0.75/0.93      (![X25 : $i, X27 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ X25 @ X27) | ((k4_xboole_0 @ X25 @ X27) != (X25)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.75/0.93  thf('18', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (((X0) != (X0))
% 0.75/0.93          | (r2_hidden @ X1 @ X0)
% 0.75/0.93          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['16', '17'])).
% 0.75/0.93  thf('19', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 0.75/0.93      inference('simplify', [status(thm)], ['18'])).
% 0.75/0.93  thf(symmetry_r1_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.75/0.93  thf('20', plain,
% 0.75/0.93      (![X11 : $i, X12 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 0.75/0.93      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.75/0.93  thf('21', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['19', '20'])).
% 0.75/0.93  thf('22', plain,
% 0.75/0.93      (![X8 : $i, X9 : $i]:
% 0.75/0.93         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.75/0.93      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.75/0.93  thf('23', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         ((r2_hidden @ X1 @ X0)
% 0.75/0.93          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/0.93  thf('24', plain,
% 0.75/0.93      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.75/0.93        | (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['15', '23'])).
% 0.75/0.93  thf('25', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.93  thf(d4_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.75/0.93       ( ![D:$i]:
% 0.75/0.93         ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.93           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.75/0.93  thf('26', plain,
% 0.75/0.93      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X6 @ X5)
% 0.75/0.93          | (r2_hidden @ X6 @ X4)
% 0.75/0.93          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.75/0.93      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.75/0.93  thf('27', plain,
% 0.75/0.93      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.75/0.93         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.75/0.93      inference('simplify', [status(thm)], ['26'])).
% 0.75/0.93  thf('28', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['25', '27'])).
% 0.75/0.93  thf('29', plain,
% 0.75/0.93      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.75/0.93        | (r2_hidden @ sk_D_1 @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['24', '28'])).
% 0.75/0.93  thf('30', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.93  thf(t100_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.93  thf('31', plain,
% 0.75/0.93      (![X17 : $i, X18 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ X17 @ X18)
% 0.75/0.93           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.93  thf('32', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ X0 @ X1)
% 0.75/0.93           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['30', '31'])).
% 0.75/0.93  thf('33', plain,
% 0.75/0.93      ((((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ k1_xboole_0))
% 0.75/0.93        | (r2_hidden @ sk_D_1 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['29', '32'])).
% 0.75/0.93  thf('34', plain,
% 0.75/0.93      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.75/0.93        | (r2_hidden @ sk_D_1 @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['24', '28'])).
% 0.75/0.93  thf('35', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.93  thf('36', plain,
% 0.75/0.93      (![X8 : $i, X10 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ X8 @ X10)
% 0.75/0.93          | ((k3_xboole_0 @ X8 @ X10) != (k1_xboole_0)))),
% 0.75/0.93      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.75/0.93  thf('37', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['35', '36'])).
% 0.75/0.93  thf('38', plain,
% 0.75/0.93      ((((k1_xboole_0) != (k1_xboole_0))
% 0.75/0.93        | (r2_hidden @ sk_D_1 @ sk_B)
% 0.75/0.93        | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['34', '37'])).
% 0.75/0.93  thf('39', plain,
% 0.75/0.93      (((r1_xboole_0 @ sk_A @ sk_B) | (r2_hidden @ sk_D_1 @ sk_B))),
% 0.75/0.93      inference('simplify', [status(thm)], ['38'])).
% 0.75/0.93  thf('40', plain,
% 0.75/0.93      (![X25 : $i, X26 : $i]:
% 0.75/0.93         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 0.75/0.93      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.75/0.93  thf('41', plain,
% 0.75/0.93      (((r2_hidden @ sk_D_1 @ sk_B) | ((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['39', '40'])).
% 0.75/0.93  thf('42', plain,
% 0.75/0.93      ((((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ k1_xboole_0))
% 0.75/0.93        | (r2_hidden @ sk_D_1 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['29', '32'])).
% 0.75/0.93  thf('43', plain,
% 0.75/0.93      ((((sk_A) = (k5_xboole_0 @ sk_A @ k1_xboole_0))
% 0.75/0.93        | (r2_hidden @ sk_D_1 @ sk_B)
% 0.75/0.93        | (r2_hidden @ sk_D_1 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['41', '42'])).
% 0.75/0.93  thf('44', plain,
% 0.75/0.93      (((r2_hidden @ sk_D_1 @ sk_B)
% 0.75/0.93        | ((sk_A) = (k5_xboole_0 @ sk_A @ k1_xboole_0)))),
% 0.75/0.93      inference('simplify', [status(thm)], ['43'])).
% 0.75/0.93  thf('45', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('46', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(t3_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.75/0.93            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.75/0.93       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.75/0.93            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.75/0.93  thf('47', plain,
% 0.75/0.93      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X15 @ X13)
% 0.75/0.93          | ~ (r2_hidden @ X15 @ X16)
% 0.75/0.93          | ~ (r1_xboole_0 @ X13 @ X16))),
% 0.75/0.93      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.75/0.93  thf('48', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D_1 @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['46', '47'])).
% 0.75/0.93  thf('49', plain, (~ (r2_hidden @ sk_D_1 @ sk_B)),
% 0.75/0.93      inference('sup-', [status(thm)], ['45', '48'])).
% 0.75/0.93  thf('50', plain, (((sk_A) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['44', '49'])).
% 0.75/0.93  thf('51', plain,
% 0.75/0.93      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)) | (r2_hidden @ sk_D_1 @ sk_B))),
% 0.75/0.93      inference('demod', [status(thm)], ['33', '50'])).
% 0.75/0.93  thf('52', plain, (~ (r2_hidden @ sk_D_1 @ sk_B)),
% 0.75/0.93      inference('sup-', [status(thm)], ['45', '48'])).
% 0.75/0.93  thf('53', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.75/0.93      inference('clc', [status(thm)], ['51', '52'])).
% 0.75/0.93  thf('54', plain,
% 0.75/0.93      (![X25 : $i, X27 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ X25 @ X27) | ((k4_xboole_0 @ X25 @ X27) != (X25)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.75/0.93  thf('55', plain, ((((sk_A) != (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['53', '54'])).
% 0.75/0.93  thf('56', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.75/0.93      inference('simplify', [status(thm)], ['55'])).
% 0.75/0.93  thf('57', plain,
% 0.75/0.93      (![X11 : $i, X12 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 0.75/0.93      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.75/0.93  thf('58', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.75/0.93      inference('sup-', [status(thm)], ['56', '57'])).
% 0.75/0.93  thf(t70_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.75/0.93            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.75/0.93       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.75/0.93            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.75/0.93  thf('59', plain,
% 0.75/0.93      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 0.75/0.93          | ~ (r1_xboole_0 @ X21 @ X22)
% 0.75/0.93          | ~ (r1_xboole_0 @ X21 @ X23))),
% 0.75/0.93      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.75/0.93  thf('60', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.75/0.93          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['58', '59'])).
% 0.75/0.93  thf('61', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['8', '60'])).
% 0.75/0.93  thf('62', plain,
% 0.75/0.93      (![X11 : $i, X12 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 0.75/0.93      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.75/0.93  thf('63', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.75/0.93      inference('sup-', [status(thm)], ['61', '62'])).
% 0.75/0.93  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 0.75/0.93  
% 0.75/0.93  % SZS output end Refutation
% 0.75/0.93  
% 0.75/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
