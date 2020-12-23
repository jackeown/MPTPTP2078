%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BaIPvusNNw

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:27 EST 2020

% Result     : Theorem 2.66s
% Output     : Refutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 136 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :   20
%              Number of atoms          :  629 (1067 expanded)
%              Number of equality atoms :   53 (  82 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','15'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('17',plain,(
    ! [X14: $i] :
      ( r1_xboole_0 @ X14 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( ( k3_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('20',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X24 ) @ X25 )
      | ( r2_hidden @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['32'])).

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

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X14: $i] :
      ( r1_xboole_0 @ X14 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('58',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['51','56','57'])).

thf('59',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['16','58'])).

thf('60',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('61',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( ( k3_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','66'])).

thf('68',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BaIPvusNNw
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 2.66/2.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.66/2.90  % Solved by: fo/fo7.sh
% 2.66/2.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.66/2.90  % done 2320 iterations in 2.425s
% 2.66/2.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.66/2.90  % SZS output start Refutation
% 2.66/2.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.66/2.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.66/2.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.66/2.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.66/2.90  thf(sk_B_type, type, sk_B: $i).
% 2.66/2.90  thf(sk_D_type, type, sk_D: $i).
% 2.66/2.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.66/2.90  thf(sk_A_type, type, sk_A: $i).
% 2.66/2.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.66/2.90  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.66/2.90  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.66/2.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.66/2.90  thf(t149_zfmisc_1, conjecture,
% 2.66/2.90    (![A:$i,B:$i,C:$i,D:$i]:
% 2.66/2.90     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.66/2.90         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.66/2.90       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.66/2.90  thf(zf_stmt_0, negated_conjecture,
% 2.66/2.90    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.66/2.90        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.66/2.90            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.66/2.90          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 2.66/2.90    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 2.66/2.90  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.66/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.90  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.66/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.90  thf(d7_xboole_0, axiom,
% 2.66/2.90    (![A:$i,B:$i]:
% 2.66/2.90     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.66/2.90       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.66/2.90  thf('2', plain,
% 2.66/2.90      (![X2 : $i, X3 : $i]:
% 2.66/2.90         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 2.66/2.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.66/2.90  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 2.66/2.90      inference('sup-', [status(thm)], ['1', '2'])).
% 2.66/2.90  thf(commutativity_k3_xboole_0, axiom,
% 2.66/2.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.66/2.90  thf('4', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.66/2.90  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 2.66/2.90      inference('demod', [status(thm)], ['3', '4'])).
% 2.66/2.90  thf('6', plain,
% 2.66/2.90      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 2.66/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.90  thf('7', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.66/2.90  thf('8', plain,
% 2.66/2.90      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 2.66/2.90      inference('demod', [status(thm)], ['6', '7'])).
% 2.66/2.90  thf(t28_xboole_1, axiom,
% 2.66/2.90    (![A:$i,B:$i]:
% 2.66/2.90     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.66/2.90  thf('9', plain,
% 2.66/2.90      (![X12 : $i, X13 : $i]:
% 2.66/2.90         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 2.66/2.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.66/2.90  thf('10', plain,
% 2.66/2.90      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 2.66/2.90         = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.66/2.90      inference('sup-', [status(thm)], ['8', '9'])).
% 2.66/2.90  thf('11', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.66/2.90  thf('12', plain,
% 2.66/2.90      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 2.66/2.90         = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.66/2.90      inference('demod', [status(thm)], ['10', '11'])).
% 2.66/2.90  thf(t16_xboole_1, axiom,
% 2.66/2.90    (![A:$i,B:$i,C:$i]:
% 2.66/2.90     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 2.66/2.90       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.66/2.90  thf('13', plain,
% 2.66/2.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.66/2.90         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 2.66/2.90           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 2.66/2.90      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.66/2.90  thf('14', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.66/2.90  thf('15', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 2.66/2.90           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['13', '14'])).
% 2.66/2.90  thf('16', plain,
% 2.66/2.90      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))
% 2.66/2.90         = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.66/2.90      inference('demod', [status(thm)], ['12', '15'])).
% 2.66/2.90  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 2.66/2.90  thf('17', plain, (![X14 : $i]: (r1_xboole_0 @ X14 @ k1_xboole_0)),
% 2.66/2.90      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.66/2.90  thf(t78_xboole_1, axiom,
% 2.66/2.90    (![A:$i,B:$i,C:$i]:
% 2.66/2.90     ( ( r1_xboole_0 @ A @ B ) =>
% 2.66/2.90       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 2.66/2.90         ( k3_xboole_0 @ A @ C ) ) ))).
% 2.66/2.90  thf('18', plain,
% 2.66/2.90      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.66/2.90         (~ (r1_xboole_0 @ X15 @ X16)
% 2.66/2.90          | ((k3_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 2.66/2.90              = (k3_xboole_0 @ X15 @ X17)))),
% 2.66/2.90      inference('cnf', [status(esa)], [t78_xboole_1])).
% 2.66/2.90  thf('19', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]:
% 2.66/2.90         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))
% 2.66/2.90           = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.90      inference('sup-', [status(thm)], ['17', '18'])).
% 2.66/2.90  thf(l27_zfmisc_1, axiom,
% 2.66/2.90    (![A:$i,B:$i]:
% 2.66/2.90     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 2.66/2.90  thf('20', plain,
% 2.66/2.90      (![X24 : $i, X25 : $i]:
% 2.66/2.90         ((r1_xboole_0 @ (k1_tarski @ X24) @ X25) | (r2_hidden @ X24 @ X25))),
% 2.66/2.90      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 2.66/2.90  thf('21', plain,
% 2.66/2.90      (![X2 : $i, X3 : $i]:
% 2.66/2.90         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 2.66/2.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.66/2.90  thf('22', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]:
% 2.66/2.90         ((r2_hidden @ X1 @ X0)
% 2.66/2.90          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 2.66/2.90      inference('sup-', [status(thm)], ['20', '21'])).
% 2.66/2.90  thf('23', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]:
% 2.66/2.90         (((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0))
% 2.66/2.90          | (r2_hidden @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['19', '22'])).
% 2.66/2.90  thf('24', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 2.66/2.90      inference('demod', [status(thm)], ['3', '4'])).
% 2.66/2.90  thf('25', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.66/2.90  thf('26', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]:
% 2.66/2.90         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))
% 2.66/2.90           = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.90      inference('sup-', [status(thm)], ['17', '18'])).
% 2.66/2.90  thf('27', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.66/2.90  thf('28', plain,
% 2.66/2.90      (![X2 : $i, X4 : $i]:
% 2.66/2.90         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 2.66/2.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.66/2.90  thf('29', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]:
% 2.66/2.90         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 2.66/2.90      inference('sup-', [status(thm)], ['27', '28'])).
% 2.66/2.90  thf('30', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]:
% 2.66/2.90         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 2.66/2.90          | (r1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X1))),
% 2.66/2.90      inference('sup-', [status(thm)], ['26', '29'])).
% 2.66/2.90  thf('31', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]:
% 2.66/2.90         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 2.66/2.90          | (r1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ X0))),
% 2.66/2.90      inference('sup-', [status(thm)], ['25', '30'])).
% 2.66/2.90  thf('32', plain,
% 2.66/2.90      ((((k1_xboole_0) != (k1_xboole_0))
% 2.66/2.90        | (r1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ sk_B) @ sk_C_1))),
% 2.66/2.90      inference('sup-', [status(thm)], ['24', '31'])).
% 2.66/2.90  thf('33', plain,
% 2.66/2.90      ((r1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ sk_B) @ sk_C_1)),
% 2.66/2.90      inference('simplify', [status(thm)], ['32'])).
% 2.66/2.90  thf(t3_xboole_0, axiom,
% 2.66/2.90    (![A:$i,B:$i]:
% 2.66/2.90     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.66/2.90            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.66/2.90       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.66/2.90            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.66/2.90  thf('34', plain,
% 2.66/2.90      (![X5 : $i, X6 : $i]:
% 2.66/2.90         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 2.66/2.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.66/2.90  thf('35', plain,
% 2.66/2.90      (![X5 : $i, X6 : $i]:
% 2.66/2.90         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X6))),
% 2.66/2.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.66/2.90  thf('36', plain,
% 2.66/2.90      (![X5 : $i, X7 : $i, X8 : $i]:
% 2.66/2.90         (~ (r2_hidden @ X7 @ X5)
% 2.66/2.90          | ~ (r2_hidden @ X7 @ X8)
% 2.66/2.90          | ~ (r1_xboole_0 @ X5 @ X8))),
% 2.66/2.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.66/2.90  thf('37', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((r1_xboole_0 @ X1 @ X0)
% 2.66/2.90          | ~ (r1_xboole_0 @ X0 @ X2)
% 2.66/2.90          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 2.66/2.90      inference('sup-', [status(thm)], ['35', '36'])).
% 2.66/2.90  thf('38', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]:
% 2.66/2.90         ((r1_xboole_0 @ X0 @ X1)
% 2.66/2.90          | ~ (r1_xboole_0 @ X1 @ X0)
% 2.66/2.90          | (r1_xboole_0 @ X0 @ X1))),
% 2.66/2.90      inference('sup-', [status(thm)], ['34', '37'])).
% 2.66/2.90  thf('39', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]:
% 2.66/2.90         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 2.66/2.90      inference('simplify', [status(thm)], ['38'])).
% 2.66/2.90  thf('40', plain,
% 2.66/2.90      ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ k1_xboole_0 @ sk_B))),
% 2.66/2.90      inference('sup-', [status(thm)], ['33', '39'])).
% 2.66/2.90  thf('41', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 2.66/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.90  thf('42', plain,
% 2.66/2.90      (![X5 : $i, X7 : $i, X8 : $i]:
% 2.66/2.90         (~ (r2_hidden @ X7 @ X5)
% 2.66/2.90          | ~ (r2_hidden @ X7 @ X8)
% 2.66/2.90          | ~ (r1_xboole_0 @ X5 @ X8))),
% 2.66/2.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.66/2.90  thf('43', plain,
% 2.66/2.90      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 2.66/2.90      inference('sup-', [status(thm)], ['41', '42'])).
% 2.66/2.90  thf('44', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ k1_xboole_0 @ sk_B))),
% 2.66/2.90      inference('sup-', [status(thm)], ['40', '43'])).
% 2.66/2.90  thf('45', plain,
% 2.66/2.90      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_xboole_0))),
% 2.66/2.90      inference('sup-', [status(thm)], ['23', '44'])).
% 2.66/2.90  thf('46', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.66/2.90  thf('47', plain,
% 2.66/2.90      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (k1_xboole_0))),
% 2.66/2.90      inference('demod', [status(thm)], ['45', '46'])).
% 2.66/2.90  thf('48', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.66/2.90  thf('49', plain,
% 2.66/2.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.66/2.90         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 2.66/2.90           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 2.66/2.90      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.66/2.90  thf('50', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 2.66/2.90           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['48', '49'])).
% 2.66/2.90  thf('51', plain,
% 2.66/2.90      (![X0 : $i]:
% 2.66/2.90         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 2.66/2.90           = (k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ X0)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['47', '50'])).
% 2.66/2.90  thf('52', plain, (![X14 : $i]: (r1_xboole_0 @ X14 @ k1_xboole_0)),
% 2.66/2.90      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.66/2.90  thf('53', plain,
% 2.66/2.90      (![X2 : $i, X3 : $i]:
% 2.66/2.90         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 2.66/2.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.66/2.90  thf('54', plain,
% 2.66/2.90      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.66/2.90      inference('sup-', [status(thm)], ['52', '53'])).
% 2.66/2.90  thf('55', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.66/2.90  thf('56', plain,
% 2.66/2.90      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['54', '55'])).
% 2.66/2.90  thf('57', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 2.66/2.90           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['13', '14'])).
% 2.66/2.90  thf('58', plain,
% 2.66/2.90      (![X0 : $i]:
% 2.66/2.90         ((k1_xboole_0)
% 2.66/2.90           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D))))),
% 2.66/2.90      inference('demod', [status(thm)], ['51', '56', '57'])).
% 2.66/2.90  thf('59', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.66/2.90      inference('demod', [status(thm)], ['16', '58'])).
% 2.66/2.90  thf('60', plain,
% 2.66/2.90      (![X2 : $i, X4 : $i]:
% 2.66/2.90         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 2.66/2.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.66/2.90  thf('61', plain,
% 2.66/2.90      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 2.66/2.90      inference('sup-', [status(thm)], ['59', '60'])).
% 2.66/2.90  thf('62', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 2.66/2.90      inference('simplify', [status(thm)], ['61'])).
% 2.66/2.90  thf('63', plain,
% 2.66/2.90      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.66/2.90         (~ (r1_xboole_0 @ X15 @ X16)
% 2.66/2.90          | ((k3_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 2.66/2.90              = (k3_xboole_0 @ X15 @ X17)))),
% 2.66/2.90      inference('cnf', [status(esa)], [t78_xboole_1])).
% 2.66/2.90  thf('64', plain,
% 2.66/2.90      (![X0 : $i]:
% 2.66/2.90         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 2.66/2.90           = (k3_xboole_0 @ sk_B @ X0))),
% 2.66/2.90      inference('sup-', [status(thm)], ['62', '63'])).
% 2.66/2.90  thf('65', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]:
% 2.66/2.90         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 2.66/2.90      inference('sup-', [status(thm)], ['27', '28'])).
% 2.66/2.90  thf('66', plain,
% 2.66/2.90      (![X0 : $i]:
% 2.66/2.90         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 2.66/2.90          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 2.66/2.90      inference('sup-', [status(thm)], ['64', '65'])).
% 2.66/2.90  thf('67', plain,
% 2.66/2.90      ((((k1_xboole_0) != (k1_xboole_0))
% 2.66/2.90        | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B))),
% 2.66/2.90      inference('sup-', [status(thm)], ['5', '66'])).
% 2.66/2.90  thf('68', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.66/2.90      inference('simplify', [status(thm)], ['67'])).
% 2.66/2.90  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 2.66/2.90  
% 2.66/2.90  % SZS output end Refutation
% 2.66/2.90  
% 2.66/2.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
