%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IzmsjyuxOt

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:29 EST 2020

% Result     : Theorem 5.11s
% Output     : Refutation 5.11s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 216 expanded)
%              Number of leaves         :   25 (  79 expanded)
%              Depth                    :   18
%              Number of atoms          :  822 (1703 expanded)
%              Number of equality atoms :   59 ( 107 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
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
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['7'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k4_xboole_0 @ X36 @ ( k1_tarski @ X37 ) )
        = X36 )
      | ( r2_hidden @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
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

thf('22',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('35',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('47',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['33','54','57'])).

thf('59',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('63',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('69',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('81',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75','78','79','84'])).

thf('86',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('87',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','90'])).

thf('92',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('93',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['0','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IzmsjyuxOt
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.11/5.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.11/5.32  % Solved by: fo/fo7.sh
% 5.11/5.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.11/5.32  % done 6916 iterations in 4.870s
% 5.11/5.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.11/5.32  % SZS output start Refutation
% 5.11/5.32  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.11/5.32  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.11/5.32  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.11/5.32  thf(sk_A_type, type, sk_A: $i).
% 5.11/5.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.11/5.32  thf(sk_B_type, type, sk_B: $i).
% 5.11/5.32  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.11/5.32  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.11/5.32  thf(sk_D_type, type, sk_D: $i).
% 5.11/5.32  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.11/5.32  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.11/5.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.11/5.32  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.11/5.32  thf(t149_zfmisc_1, conjecture,
% 5.11/5.32    (![A:$i,B:$i,C:$i,D:$i]:
% 5.11/5.32     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 5.11/5.32         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 5.11/5.32       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 5.11/5.32  thf(zf_stmt_0, negated_conjecture,
% 5.11/5.32    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 5.11/5.32        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 5.11/5.32            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 5.11/5.32          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 5.11/5.32    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 5.11/5.32  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 5.11/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.32  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 5.11/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.32  thf(d7_xboole_0, axiom,
% 5.11/5.32    (![A:$i,B:$i]:
% 5.11/5.32     ( ( r1_xboole_0 @ A @ B ) <=>
% 5.11/5.32       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 5.11/5.32  thf('2', plain,
% 5.11/5.32      (![X2 : $i, X3 : $i]:
% 5.11/5.32         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 5.11/5.32      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.11/5.32  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 5.11/5.32      inference('sup-', [status(thm)], ['1', '2'])).
% 5.11/5.32  thf(commutativity_k3_xboole_0, axiom,
% 5.11/5.32    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.11/5.32  thf('4', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.11/5.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.11/5.32  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 5.11/5.32      inference('demod', [status(thm)], ['3', '4'])).
% 5.11/5.32  thf('6', plain,
% 5.11/5.32      (![X2 : $i, X4 : $i]:
% 5.11/5.32         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 5.11/5.32      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.11/5.32  thf('7', plain,
% 5.11/5.32      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 5.11/5.32      inference('sup-', [status(thm)], ['5', '6'])).
% 5.11/5.32  thf('8', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 5.11/5.32      inference('simplify', [status(thm)], ['7'])).
% 5.11/5.32  thf(t65_zfmisc_1, axiom,
% 5.11/5.32    (![A:$i,B:$i]:
% 5.11/5.32     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 5.11/5.32       ( ~( r2_hidden @ B @ A ) ) ))).
% 5.11/5.32  thf('9', plain,
% 5.11/5.32      (![X36 : $i, X37 : $i]:
% 5.11/5.32         (((k4_xboole_0 @ X36 @ (k1_tarski @ X37)) = (X36))
% 5.11/5.32          | (r2_hidden @ X37 @ X36))),
% 5.11/5.32      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 5.11/5.32  thf(t79_xboole_1, axiom,
% 5.11/5.32    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 5.11/5.32  thf('10', plain,
% 5.11/5.32      (![X24 : $i, X25 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ X25)),
% 5.11/5.32      inference('cnf', [status(esa)], [t79_xboole_1])).
% 5.11/5.32  thf(symmetry_r1_xboole_0, axiom,
% 5.11/5.32    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 5.11/5.32  thf('11', plain,
% 5.11/5.32      (![X5 : $i, X6 : $i]:
% 5.11/5.32         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 5.11/5.32      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.11/5.32  thf('12', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 5.11/5.32      inference('sup-', [status(thm)], ['10', '11'])).
% 5.11/5.32  thf('13', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i]:
% 5.11/5.32         ((r1_xboole_0 @ (k1_tarski @ X1) @ X0) | (r2_hidden @ X1 @ X0))),
% 5.11/5.32      inference('sup+', [status(thm)], ['9', '12'])).
% 5.11/5.32  thf(t70_xboole_1, axiom,
% 5.11/5.32    (![A:$i,B:$i,C:$i]:
% 5.11/5.32     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 5.11/5.32            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 5.11/5.32       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 5.11/5.32            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 5.11/5.32  thf('14', plain,
% 5.11/5.32      (![X20 : $i, X21 : $i, X23 : $i]:
% 5.11/5.32         ((r1_xboole_0 @ X20 @ X21)
% 5.11/5.32          | ~ (r1_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X23)))),
% 5.11/5.32      inference('cnf', [status(esa)], [t70_xboole_1])).
% 5.11/5.32  thf('15', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.11/5.32         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 5.11/5.32          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 5.11/5.32      inference('sup-', [status(thm)], ['13', '14'])).
% 5.11/5.32  thf('16', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 5.11/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.32  thf('17', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 5.11/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.32  thf('18', plain,
% 5.11/5.32      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.11/5.32         ((r1_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 5.11/5.32          | ~ (r1_xboole_0 @ X20 @ X21)
% 5.11/5.32          | ~ (r1_xboole_0 @ X20 @ X22))),
% 5.11/5.32      inference('cnf', [status(esa)], [t70_xboole_1])).
% 5.11/5.32  thf('19', plain,
% 5.11/5.32      (![X0 : $i]:
% 5.11/5.32         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 5.11/5.32          | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 5.11/5.32      inference('sup-', [status(thm)], ['17', '18'])).
% 5.11/5.32  thf('20', plain, ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 5.11/5.32      inference('sup-', [status(thm)], ['16', '19'])).
% 5.11/5.32  thf('21', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 5.11/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.32  thf(t3_xboole_0, axiom,
% 5.11/5.32    (![A:$i,B:$i]:
% 5.11/5.32     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 5.11/5.32            ( r1_xboole_0 @ A @ B ) ) ) & 
% 5.11/5.32       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 5.11/5.32            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 5.11/5.32  thf('22', plain,
% 5.11/5.32      (![X7 : $i, X9 : $i, X10 : $i]:
% 5.11/5.32         (~ (r2_hidden @ X9 @ X7)
% 5.11/5.32          | ~ (r2_hidden @ X9 @ X10)
% 5.11/5.32          | ~ (r1_xboole_0 @ X7 @ X10))),
% 5.11/5.32      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.11/5.32  thf('23', plain,
% 5.11/5.32      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 5.11/5.32      inference('sup-', [status(thm)], ['21', '22'])).
% 5.11/5.32  thf('24', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 5.11/5.32      inference('sup-', [status(thm)], ['20', '23'])).
% 5.11/5.32  thf('25', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 5.11/5.32      inference('sup-', [status(thm)], ['15', '24'])).
% 5.11/5.32  thf('26', plain,
% 5.11/5.32      (![X2 : $i, X3 : $i]:
% 5.11/5.32         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 5.11/5.32      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.11/5.32  thf('27', plain,
% 5.11/5.32      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_xboole_0))),
% 5.11/5.32      inference('sup-', [status(thm)], ['25', '26'])).
% 5.11/5.32  thf('28', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.11/5.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.11/5.32  thf('29', plain,
% 5.11/5.32      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (k1_xboole_0))),
% 5.11/5.32      inference('demod', [status(thm)], ['27', '28'])).
% 5.11/5.32  thf('30', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.11/5.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.11/5.32  thf(t16_xboole_1, axiom,
% 5.11/5.32    (![A:$i,B:$i,C:$i]:
% 5.11/5.32     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 5.11/5.32       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 5.11/5.32  thf('31', plain,
% 5.11/5.32      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.11/5.32         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 5.11/5.32           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 5.11/5.32      inference('cnf', [status(esa)], [t16_xboole_1])).
% 5.11/5.32  thf('32', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.11/5.32         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 5.11/5.32           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 5.11/5.32      inference('sup+', [status(thm)], ['30', '31'])).
% 5.11/5.32  thf('33', plain,
% 5.11/5.32      (![X0 : $i]:
% 5.11/5.32         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 5.11/5.32           = (k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ X0)))),
% 5.11/5.32      inference('sup+', [status(thm)], ['29', '32'])).
% 5.11/5.32  thf('34', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 5.11/5.32      inference('sup-', [status(thm)], ['10', '11'])).
% 5.11/5.32  thf(t83_xboole_1, axiom,
% 5.11/5.32    (![A:$i,B:$i]:
% 5.11/5.32     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.11/5.32  thf('35', plain,
% 5.11/5.32      (![X26 : $i, X27 : $i]:
% 5.11/5.32         (((k4_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_xboole_0 @ X26 @ X27))),
% 5.11/5.32      inference('cnf', [status(esa)], [t83_xboole_1])).
% 5.11/5.32  thf('36', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i]:
% 5.11/5.32         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 5.11/5.32      inference('sup-', [status(thm)], ['34', '35'])).
% 5.11/5.32  thf(t36_xboole_1, axiom,
% 5.11/5.32    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 5.11/5.32  thf('37', plain,
% 5.11/5.32      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 5.11/5.32      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.11/5.32  thf('38', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 5.11/5.32      inference('sup+', [status(thm)], ['36', '37'])).
% 5.11/5.32  thf(t28_xboole_1, axiom,
% 5.11/5.32    (![A:$i,B:$i]:
% 5.11/5.32     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.11/5.32  thf('39', plain,
% 5.11/5.32      (![X14 : $i, X15 : $i]:
% 5.11/5.32         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 5.11/5.32      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.11/5.32  thf('40', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 5.11/5.32      inference('sup-', [status(thm)], ['38', '39'])).
% 5.11/5.32  thf('41', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.11/5.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.11/5.32  thf('42', plain,
% 5.11/5.32      (![X2 : $i, X4 : $i]:
% 5.11/5.32         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 5.11/5.32      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.11/5.32  thf('43', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i]:
% 5.11/5.32         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 5.11/5.32      inference('sup-', [status(thm)], ['41', '42'])).
% 5.11/5.32  thf('44', plain,
% 5.11/5.32      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 5.11/5.32      inference('sup-', [status(thm)], ['40', '43'])).
% 5.11/5.32  thf('45', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 5.11/5.32      inference('simplify', [status(thm)], ['44'])).
% 5.11/5.32  thf('46', plain,
% 5.11/5.32      (![X7 : $i, X8 : $i]:
% 5.11/5.32         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 5.11/5.32      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.11/5.32  thf('47', plain,
% 5.11/5.32      (![X7 : $i, X8 : $i]:
% 5.11/5.32         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 5.11/5.32      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.11/5.32  thf('48', plain,
% 5.11/5.32      (![X7 : $i, X9 : $i, X10 : $i]:
% 5.11/5.32         (~ (r2_hidden @ X9 @ X7)
% 5.11/5.32          | ~ (r2_hidden @ X9 @ X10)
% 5.11/5.32          | ~ (r1_xboole_0 @ X7 @ X10))),
% 5.11/5.32      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.11/5.32  thf('49', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.11/5.32         ((r1_xboole_0 @ X0 @ X1)
% 5.11/5.32          | ~ (r1_xboole_0 @ X0 @ X2)
% 5.11/5.32          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 5.11/5.32      inference('sup-', [status(thm)], ['47', '48'])).
% 5.11/5.32  thf('50', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i]:
% 5.11/5.32         ((r1_xboole_0 @ X0 @ X1)
% 5.11/5.32          | ~ (r1_xboole_0 @ X0 @ X0)
% 5.11/5.32          | (r1_xboole_0 @ X0 @ X1))),
% 5.11/5.32      inference('sup-', [status(thm)], ['46', '49'])).
% 5.11/5.32  thf('51', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i]:
% 5.11/5.32         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 5.11/5.32      inference('simplify', [status(thm)], ['50'])).
% 5.11/5.32  thf('52', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 5.11/5.32      inference('sup-', [status(thm)], ['45', '51'])).
% 5.11/5.32  thf('53', plain,
% 5.11/5.32      (![X2 : $i, X3 : $i]:
% 5.11/5.32         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 5.11/5.32      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.11/5.32  thf('54', plain,
% 5.11/5.32      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.11/5.32      inference('sup-', [status(thm)], ['52', '53'])).
% 5.11/5.32  thf('55', plain,
% 5.11/5.32      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.11/5.32         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 5.11/5.32           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 5.11/5.32      inference('cnf', [status(esa)], [t16_xboole_1])).
% 5.11/5.32  thf('56', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.11/5.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.11/5.32  thf('57', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.11/5.32         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 5.11/5.32           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.11/5.32      inference('sup+', [status(thm)], ['55', '56'])).
% 5.11/5.32  thf('58', plain,
% 5.11/5.32      (![X0 : $i]:
% 5.11/5.32         ((k1_xboole_0)
% 5.11/5.32           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D))))),
% 5.11/5.32      inference('demod', [status(thm)], ['33', '54', '57'])).
% 5.11/5.32  thf('59', plain,
% 5.11/5.32      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 5.11/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.32  thf('60', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.11/5.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.11/5.32  thf('61', plain,
% 5.11/5.32      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 5.11/5.32      inference('demod', [status(thm)], ['59', '60'])).
% 5.11/5.32  thf('62', plain,
% 5.11/5.32      (![X14 : $i, X15 : $i]:
% 5.11/5.32         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 5.11/5.32      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.11/5.32  thf('63', plain,
% 5.11/5.32      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 5.11/5.33         = (k3_xboole_0 @ sk_B @ sk_A))),
% 5.11/5.33      inference('sup-', [status(thm)], ['61', '62'])).
% 5.11/5.33  thf('64', plain,
% 5.11/5.33      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.11/5.33      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.11/5.33  thf('65', plain,
% 5.11/5.33      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 5.11/5.33         = (k3_xboole_0 @ sk_B @ sk_A))),
% 5.11/5.33      inference('demod', [status(thm)], ['63', '64'])).
% 5.11/5.33  thf('66', plain,
% 5.11/5.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.11/5.33         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 5.11/5.33           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 5.11/5.33      inference('cnf', [status(esa)], [t16_xboole_1])).
% 5.11/5.33  thf('67', plain,
% 5.11/5.33      (![X0 : $i]:
% 5.11/5.33         ((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 5.11/5.33           = (k3_xboole_0 @ (k1_tarski @ sk_D) @ 
% 5.11/5.33              (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)))),
% 5.11/5.33      inference('sup+', [status(thm)], ['65', '66'])).
% 5.11/5.33  thf('68', plain,
% 5.11/5.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.11/5.33         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 5.11/5.33           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 5.11/5.33      inference('cnf', [status(esa)], [t16_xboole_1])).
% 5.11/5.33  thf('69', plain,
% 5.11/5.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.11/5.33         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 5.11/5.33           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 5.11/5.33      inference('cnf', [status(esa)], [t16_xboole_1])).
% 5.11/5.33  thf('70', plain,
% 5.11/5.33      (![X0 : $i]:
% 5.11/5.33         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 5.11/5.33           = (k3_xboole_0 @ (k1_tarski @ sk_D) @ 
% 5.11/5.33              (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))))),
% 5.11/5.33      inference('demod', [status(thm)], ['67', '68', '69'])).
% 5.11/5.33  thf('71', plain,
% 5.11/5.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.11/5.33         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 5.11/5.33           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.11/5.33      inference('sup+', [status(thm)], ['55', '56'])).
% 5.11/5.33  thf('72', plain,
% 5.11/5.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.11/5.33         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 5.11/5.33           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 5.11/5.33      inference('sup+', [status(thm)], ['30', '31'])).
% 5.11/5.33  thf('73', plain,
% 5.11/5.33      (![X0 : $i]:
% 5.11/5.33         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 5.11/5.33           = (k3_xboole_0 @ sk_B @ 
% 5.11/5.33              (k3_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))))),
% 5.11/5.33      inference('demod', [status(thm)], ['70', '71', '72'])).
% 5.11/5.33  thf('74', plain,
% 5.11/5.33      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))
% 5.11/5.33         = (k3_xboole_0 @ sk_B @ k1_xboole_0))),
% 5.11/5.33      inference('sup+', [status(thm)], ['58', '73'])).
% 5.11/5.33  thf('75', plain,
% 5.11/5.33      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.11/5.33      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.11/5.33  thf('76', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 5.11/5.33      inference('sup-', [status(thm)], ['38', '39'])).
% 5.11/5.33  thf('77', plain,
% 5.11/5.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.11/5.33         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 5.11/5.33           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.11/5.33      inference('sup+', [status(thm)], ['55', '56'])).
% 5.11/5.33  thf('78', plain,
% 5.11/5.33      (![X0 : $i, X1 : $i]:
% 5.11/5.33         ((k3_xboole_0 @ X1 @ X0)
% 5.11/5.33           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 5.11/5.33      inference('sup+', [status(thm)], ['76', '77'])).
% 5.11/5.33  thf('79', plain,
% 5.11/5.33      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.11/5.33      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.11/5.33  thf('80', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 5.11/5.33      inference('sup-', [status(thm)], ['45', '51'])).
% 5.11/5.33  thf('81', plain,
% 5.11/5.33      (![X5 : $i, X6 : $i]:
% 5.11/5.33         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 5.11/5.33      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.11/5.33  thf('82', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 5.11/5.33      inference('sup-', [status(thm)], ['80', '81'])).
% 5.11/5.33  thf('83', plain,
% 5.11/5.33      (![X2 : $i, X3 : $i]:
% 5.11/5.33         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 5.11/5.33      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.11/5.33  thf('84', plain,
% 5.11/5.33      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 5.11/5.33      inference('sup-', [status(thm)], ['82', '83'])).
% 5.11/5.33  thf('85', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 5.11/5.33      inference('demod', [status(thm)], ['74', '75', '78', '79', '84'])).
% 5.11/5.33  thf('86', plain,
% 5.11/5.33      (![X2 : $i, X4 : $i]:
% 5.11/5.33         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 5.11/5.33      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.11/5.33  thf('87', plain,
% 5.11/5.33      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 5.11/5.33      inference('sup-', [status(thm)], ['85', '86'])).
% 5.11/5.33  thf('88', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 5.11/5.33      inference('simplify', [status(thm)], ['87'])).
% 5.11/5.33  thf('89', plain,
% 5.11/5.33      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.11/5.33         ((r1_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 5.11/5.33          | ~ (r1_xboole_0 @ X20 @ X21)
% 5.11/5.33          | ~ (r1_xboole_0 @ X20 @ X22))),
% 5.11/5.33      inference('cnf', [status(esa)], [t70_xboole_1])).
% 5.11/5.33  thf('90', plain,
% 5.11/5.33      (![X0 : $i]:
% 5.11/5.33         (~ (r1_xboole_0 @ sk_B @ X0)
% 5.11/5.33          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 5.11/5.33      inference('sup-', [status(thm)], ['88', '89'])).
% 5.11/5.33  thf('91', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 5.11/5.33      inference('sup-', [status(thm)], ['8', '90'])).
% 5.11/5.33  thf('92', plain,
% 5.11/5.33      (![X5 : $i, X6 : $i]:
% 5.11/5.33         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 5.11/5.33      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.11/5.33  thf('93', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 5.11/5.33      inference('sup-', [status(thm)], ['91', '92'])).
% 5.11/5.33  thf('94', plain, ($false), inference('demod', [status(thm)], ['0', '93'])).
% 5.11/5.33  
% 5.11/5.33  % SZS output end Refutation
% 5.11/5.33  
% 5.11/5.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
