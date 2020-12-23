%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.shpecKvP7n

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:36 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  177 (2020 expanded)
%              Number of leaves         :   26 ( 642 expanded)
%              Depth                    :   39
%              Number of atoms          : 1331 (20288 expanded)
%              Number of equality atoms :  199 (2799 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('0',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ( k2_zfmisc_1 @ X34 @ ( k4_xboole_0 @ X31 @ X33 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X31 ) @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf(t134_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ C @ D ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( ( A = C )
            & ( B = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t134_zfmisc_1])).

thf('1',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X31 @ X33 ) @ X32 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X31 @ X32 ) @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X35 @ X36 ) @ ( k2_zfmisc_1 @ X37 @ X38 ) )
      | ~ ( r1_xboole_0 @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ X3 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X25 @ X24 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,
    ( ( ( k2_zfmisc_1 @ sk_C_1 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) )
     != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k2_zfmisc_1 @ sk_C_1 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) )
     != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','23'])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X31 @ X33 ) @ X32 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X31 @ X32 ) @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_zfmisc_1 @ X25 @ X26 )
        = k1_xboole_0 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('38',plain,(
    ! [X26: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X26 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','40'])).

thf('42',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('43',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X25 @ X24 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_D @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ sk_D @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('54',plain,
    ( sk_D
    = ( k3_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('58',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('62',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X13 = X12 )
      | ( ( k4_xboole_0 @ X13 @ X12 )
       != ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
     != k1_xboole_0 )
    | ( sk_B_1
      = ( k3_xboole_0 @ sk_D @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,
    ( sk_D
    = ( k3_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('66',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
     != k1_xboole_0 )
    | ( sk_B_1 = sk_D ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X31 @ X33 ) @ X32 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X31 @ X32 ) @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('68',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ( k2_zfmisc_1 @ X34 @ ( k4_xboole_0 @ X31 @ X33 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X31 ) @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_D ) )
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) @ sk_D ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('73',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('79',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('80',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('86',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('89',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('91',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X27 @ X29 ) @ ( k3_xboole_0 @ X28 @ X30 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('92',plain,
    ( sk_D
    = ( k3_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ X0 @ sk_A ) ) @ sk_D ) ) ),
    inference('sup+',[status(thm)],['84','93'])).

thf('95',plain,(
    ! [X26: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X26 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('96',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ X0 @ sk_A ) ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) @ sk_D ) ),
    inference('sup+',[status(thm)],['77','96'])).

thf('98',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('101',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_D ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('104',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('105',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('108',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ sk_D )
    = ( k2_zfmisc_1 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['101','102','108'])).

thf('110',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) @ sk_D ) ),
    inference('sup+',[status(thm)],['77','96'])).

thf('111',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X25 @ X24 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('112',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('115',plain,
    ( ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('117',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('118',plain,
    ( ( sk_C_1 = sk_A )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_zfmisc_1 @ X25 @ X26 )
        = k1_xboole_0 )
      | ( X26 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('120',plain,(
    ! [X25: $i] :
      ( ( k2_zfmisc_1 @ X25 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_D )
        = k1_xboole_0 )
      | ( sk_C_1 = sk_A ) ) ),
    inference('sup+',[status(thm)],['118','120'])).

thf('122',plain,
    ( ( ( k2_zfmisc_1 @ sk_C_1 @ sk_D )
      = k1_xboole_0 )
    | ( sk_C_1 = sk_A ) ),
    inference('sup+',[status(thm)],['109','121'])).

thf('123',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X25 @ X24 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('125',plain,
    ( ( ( k2_zfmisc_1 @ sk_C_1 @ sk_D )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ( k2_zfmisc_1 @ sk_C_1 @ sk_D )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['125','126','127'])).

thf('129',plain,(
    sk_C_1 = sk_A ),
    inference('simplify_reflect-',[status(thm)],['122','128'])).

thf('130',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['98','129'])).

thf('131',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X25 @ X24 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('132',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    sk_C_1 = sk_A ),
    inference('simplify_reflect-',[status(thm)],['122','128'])).

thf('136',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['133','136'])).

thf('138',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B_1 = sk_D ) ),
    inference(demod,[status(thm)],['66','137'])).

thf('139',plain,(
    sk_B_1 = sk_D ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B_1 != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( sk_B_1 != sk_D )
   <= ( sk_B_1 != sk_D ) ),
    inference(split,[status(esa)],['140'])).

thf('142',plain,(
    sk_C_1 = sk_A ),
    inference('simplify_reflect-',[status(thm)],['122','128'])).

thf('143',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['140'])).

thf('144',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    sk_A = sk_C_1 ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( sk_B_1 != sk_D )
    | ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['140'])).

thf('147',plain,(
    sk_B_1 != sk_D ),
    inference('sat_resolution*',[status(thm)],['145','146'])).

thf('148',plain,(
    sk_B_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['141','147'])).

thf('149',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['139','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.shpecKvP7n
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:54:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.65/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.88  % Solved by: fo/fo7.sh
% 0.65/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.88  % done 990 iterations in 0.404s
% 0.65/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.88  % SZS output start Refutation
% 0.65/0.88  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.65/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.65/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.65/0.88  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.65/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.65/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.65/0.88  thf(sk_B_type, type, sk_B: $i > $i).
% 0.65/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.65/0.88  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.65/0.88  thf(sk_D_type, type, sk_D: $i).
% 0.65/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.65/0.88  thf(t125_zfmisc_1, axiom,
% 0.65/0.88    (![A:$i,B:$i,C:$i]:
% 0.65/0.88     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.65/0.88         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.65/0.88       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.65/0.88         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.65/0.88  thf('0', plain,
% 0.65/0.88      (![X31 : $i, X33 : $i, X34 : $i]:
% 0.65/0.88         ((k2_zfmisc_1 @ X34 @ (k4_xboole_0 @ X31 @ X33))
% 0.65/0.88           = (k4_xboole_0 @ (k2_zfmisc_1 @ X34 @ X31) @ 
% 0.65/0.88              (k2_zfmisc_1 @ X34 @ X33)))),
% 0.65/0.88      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.65/0.88  thf(t134_zfmisc_1, conjecture,
% 0.65/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.88     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.65/0.88       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.65/0.88         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.65/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.88    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.88        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.65/0.88          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.65/0.88            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 0.65/0.88    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 0.65/0.88  thf('1', plain,
% 0.65/0.88      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('2', plain,
% 0.65/0.88      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.65/0.88         ((k2_zfmisc_1 @ (k4_xboole_0 @ X31 @ X33) @ X32)
% 0.65/0.88           = (k4_xboole_0 @ (k2_zfmisc_1 @ X31 @ X32) @ 
% 0.65/0.88              (k2_zfmisc_1 @ X33 @ X32)))),
% 0.65/0.88      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.65/0.88  thf('3', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         ((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 0.65/0.88           = (k4_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 0.65/0.88              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 0.65/0.88      inference('sup+', [status(thm)], ['1', '2'])).
% 0.65/0.88  thf('4', plain,
% 0.65/0.88      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_B_1)
% 0.65/0.88         = (k2_zfmisc_1 @ sk_C_1 @ (k4_xboole_0 @ sk_D @ sk_B_1)))),
% 0.65/0.88      inference('sup+', [status(thm)], ['0', '3'])).
% 0.65/0.88  thf(t79_xboole_1, axiom,
% 0.65/0.88    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.65/0.88  thf('5', plain,
% 0.65/0.88      (![X19 : $i, X20 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X20)),
% 0.65/0.88      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.65/0.88  thf(t127_zfmisc_1, axiom,
% 0.65/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.88     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.65/0.88       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.65/0.88  thf('6', plain,
% 0.65/0.88      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.65/0.88         ((r1_xboole_0 @ (k2_zfmisc_1 @ X35 @ X36) @ (k2_zfmisc_1 @ X37 @ X38))
% 0.65/0.88          | ~ (r1_xboole_0 @ X35 @ X37))),
% 0.65/0.88      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.65/0.88  thf('7', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.65/0.88         (r1_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0) @ X3) @ 
% 0.65/0.88          (k2_zfmisc_1 @ X0 @ X2))),
% 0.65/0.88      inference('sup-', [status(thm)], ['5', '6'])).
% 0.65/0.88  thf('8', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (r1_xboole_0 @ 
% 0.65/0.88          (k2_zfmisc_1 @ sk_C_1 @ (k4_xboole_0 @ sk_D @ sk_B_1)) @ 
% 0.65/0.88          (k2_zfmisc_1 @ sk_C_1 @ X0))),
% 0.65/0.88      inference('sup+', [status(thm)], ['4', '7'])).
% 0.65/0.88  thf(t7_xboole_0, axiom,
% 0.65/0.88    (![A:$i]:
% 0.65/0.88     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.65/0.88          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.65/0.88  thf('9', plain,
% 0.65/0.88      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.65/0.88      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.65/0.88  thf(t3_boole, axiom,
% 0.65/0.88    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.65/0.88  thf('10', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.65/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.88  thf(t36_xboole_1, axiom,
% 0.65/0.88    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.65/0.88  thf('11', plain,
% 0.65/0.88      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.65/0.88      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.65/0.88  thf('12', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.65/0.88      inference('sup+', [status(thm)], ['10', '11'])).
% 0.65/0.88  thf(l32_xboole_1, axiom,
% 0.65/0.88    (![A:$i,B:$i]:
% 0.65/0.88     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.65/0.88  thf('13', plain,
% 0.65/0.88      (![X9 : $i, X11 : $i]:
% 0.65/0.88         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.65/0.88      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.65/0.88  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.65/0.88      inference('sup-', [status(thm)], ['12', '13'])).
% 0.65/0.88  thf(t48_xboole_1, axiom,
% 0.65/0.88    (![A:$i,B:$i]:
% 0.65/0.88     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.65/0.88  thf('15', plain,
% 0.65/0.88      (![X17 : $i, X18 : $i]:
% 0.65/0.88         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.65/0.88           = (k3_xboole_0 @ X17 @ X18))),
% 0.65/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.65/0.88  thf('16', plain,
% 0.65/0.88      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.65/0.88      inference('sup+', [status(thm)], ['14', '15'])).
% 0.65/0.88  thf('17', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.65/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.88  thf('18', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.65/0.88      inference('demod', [status(thm)], ['16', '17'])).
% 0.65/0.88  thf(commutativity_k3_xboole_0, axiom,
% 0.65/0.88    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.65/0.88  thf('19', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.65/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.65/0.88  thf(t4_xboole_0, axiom,
% 0.65/0.88    (![A:$i,B:$i]:
% 0.65/0.88     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.65/0.88            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.65/0.88       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.65/0.88            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.65/0.88  thf('20', plain,
% 0.65/0.88      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.65/0.88         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.65/0.88          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.65/0.88      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.65/0.88  thf('21', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.88         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.65/0.88          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.65/0.88      inference('sup-', [status(thm)], ['19', '20'])).
% 0.65/0.88  thf('22', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i]:
% 0.65/0.88         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.65/0.88      inference('sup-', [status(thm)], ['18', '21'])).
% 0.65/0.88  thf('23', plain,
% 0.65/0.88      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.65/0.88      inference('sup-', [status(thm)], ['9', '22'])).
% 0.65/0.88  thf('24', plain,
% 0.65/0.88      (((k2_zfmisc_1 @ sk_C_1 @ (k4_xboole_0 @ sk_D @ sk_B_1)) = (k1_xboole_0))),
% 0.65/0.88      inference('sup-', [status(thm)], ['8', '23'])).
% 0.65/0.88  thf('25', plain,
% 0.65/0.88      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_B_1)
% 0.65/0.88         = (k2_zfmisc_1 @ sk_C_1 @ (k4_xboole_0 @ sk_D @ sk_B_1)))),
% 0.65/0.88      inference('sup+', [status(thm)], ['0', '3'])).
% 0.65/0.88  thf(t113_zfmisc_1, axiom,
% 0.65/0.88    (![A:$i,B:$i]:
% 0.65/0.88     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.65/0.88       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.65/0.88  thf('26', plain,
% 0.65/0.88      (![X24 : $i, X25 : $i]:
% 0.65/0.88         (((X24) = (k1_xboole_0))
% 0.65/0.88          | ((X25) = (k1_xboole_0))
% 0.65/0.88          | ((k2_zfmisc_1 @ X25 @ X24) != (k1_xboole_0)))),
% 0.65/0.88      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.65/0.88  thf('27', plain,
% 0.65/0.88      ((((k2_zfmisc_1 @ sk_C_1 @ (k4_xboole_0 @ sk_D @ sk_B_1))
% 0.65/0.88          != (k1_xboole_0))
% 0.65/0.88        | ((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 0.65/0.88        | ((sk_B_1) = (k1_xboole_0)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['25', '26'])).
% 0.65/0.88  thf('28', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('29', plain,
% 0.65/0.88      ((((k2_zfmisc_1 @ sk_C_1 @ (k4_xboole_0 @ sk_D @ sk_B_1))
% 0.65/0.88          != (k1_xboole_0))
% 0.65/0.88        | ((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 0.65/0.88      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.65/0.88  thf('30', plain,
% 0.65/0.88      (((k2_zfmisc_1 @ sk_C_1 @ (k4_xboole_0 @ sk_D @ sk_B_1)) = (k1_xboole_0))),
% 0.65/0.88      inference('sup-', [status(thm)], ['8', '23'])).
% 0.65/0.88  thf('31', plain,
% 0.65/0.88      ((((k1_xboole_0) != (k1_xboole_0))
% 0.65/0.88        | ((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 0.65/0.88      inference('demod', [status(thm)], ['29', '30'])).
% 0.65/0.88  thf('32', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.65/0.88      inference('simplify', [status(thm)], ['31'])).
% 0.65/0.88  thf('33', plain,
% 0.65/0.88      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.65/0.88         ((k2_zfmisc_1 @ (k4_xboole_0 @ X31 @ X33) @ X32)
% 0.65/0.88           = (k4_xboole_0 @ (k2_zfmisc_1 @ X31 @ X32) @ 
% 0.65/0.88              (k2_zfmisc_1 @ X33 @ X32)))),
% 0.65/0.88      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.65/0.88  thf('34', plain,
% 0.65/0.88      (![X9 : $i, X10 : $i]:
% 0.65/0.88         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 0.65/0.88      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.65/0.88  thf('35', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.88         (((k2_zfmisc_1 @ (k4_xboole_0 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 0.65/0.88          | (r1_tarski @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['33', '34'])).
% 0.65/0.88  thf('36', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.65/0.88          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 0.65/0.88             (k2_zfmisc_1 @ sk_C_1 @ X0)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['32', '35'])).
% 0.65/0.88  thf('37', plain,
% 0.65/0.88      (![X25 : $i, X26 : $i]:
% 0.65/0.88         (((k2_zfmisc_1 @ X25 @ X26) = (k1_xboole_0))
% 0.65/0.88          | ((X25) != (k1_xboole_0)))),
% 0.65/0.88      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.65/0.88  thf('38', plain,
% 0.65/0.88      (![X26 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X26) = (k1_xboole_0))),
% 0.65/0.88      inference('simplify', [status(thm)], ['37'])).
% 0.65/0.88  thf('39', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (((k1_xboole_0) != (k1_xboole_0))
% 0.65/0.88          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 0.65/0.88             (k2_zfmisc_1 @ sk_C_1 @ X0)))),
% 0.65/0.88      inference('demod', [status(thm)], ['36', '38'])).
% 0.65/0.88  thf('40', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ (k2_zfmisc_1 @ sk_C_1 @ X0))),
% 0.65/0.88      inference('simplify', [status(thm)], ['39'])).
% 0.65/0.88  thf('41', plain,
% 0.65/0.88      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B_1)) @ 
% 0.65/0.88        k1_xboole_0)),
% 0.65/0.88      inference('sup+', [status(thm)], ['24', '40'])).
% 0.65/0.88  thf('42', plain,
% 0.65/0.88      (![X9 : $i, X11 : $i]:
% 0.65/0.88         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.65/0.88      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.65/0.88  thf('43', plain,
% 0.65/0.88      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B_1)) @ 
% 0.65/0.88         k1_xboole_0) = (k1_xboole_0))),
% 0.65/0.88      inference('sup-', [status(thm)], ['41', '42'])).
% 0.65/0.88  thf('44', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.65/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.88  thf('45', plain,
% 0.65/0.88      (((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B_1)) = (k1_xboole_0))),
% 0.65/0.88      inference('demod', [status(thm)], ['43', '44'])).
% 0.65/0.88  thf('46', plain,
% 0.65/0.88      (![X24 : $i, X25 : $i]:
% 0.65/0.88         (((X24) = (k1_xboole_0))
% 0.65/0.88          | ((X25) = (k1_xboole_0))
% 0.65/0.88          | ((k2_zfmisc_1 @ X25 @ X24) != (k1_xboole_0)))),
% 0.65/0.88      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.65/0.88  thf('47', plain,
% 0.65/0.88      ((((k1_xboole_0) != (k1_xboole_0))
% 0.65/0.88        | ((sk_A) = (k1_xboole_0))
% 0.65/0.88        | ((k4_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['45', '46'])).
% 0.65/0.88  thf('48', plain,
% 0.65/0.88      ((((k4_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))
% 0.65/0.88        | ((sk_A) = (k1_xboole_0)))),
% 0.65/0.88      inference('simplify', [status(thm)], ['47'])).
% 0.65/0.88  thf('49', plain, (((sk_A) != (k1_xboole_0))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('50', plain, (((k4_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))),
% 0.65/0.88      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.65/0.88  thf('51', plain,
% 0.65/0.88      (![X17 : $i, X18 : $i]:
% 0.65/0.88         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.65/0.88           = (k3_xboole_0 @ X17 @ X18))),
% 0.65/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.65/0.88  thf('52', plain,
% 0.65/0.88      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k3_xboole_0 @ sk_D @ sk_B_1))),
% 0.65/0.88      inference('sup+', [status(thm)], ['50', '51'])).
% 0.65/0.88  thf('53', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.65/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.88  thf('54', plain, (((sk_D) = (k3_xboole_0 @ sk_D @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['52', '53'])).
% 0.65/0.88  thf('55', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.65/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.65/0.88  thf('56', plain,
% 0.65/0.88      (![X17 : $i, X18 : $i]:
% 0.65/0.88         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.65/0.88           = (k3_xboole_0 @ X17 @ X18))),
% 0.65/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.65/0.88  thf('57', plain,
% 0.65/0.88      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.65/0.88      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.65/0.88  thf('58', plain,
% 0.65/0.88      (![X9 : $i, X11 : $i]:
% 0.65/0.88         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.65/0.88      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.65/0.88  thf('59', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i]:
% 0.65/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.65/0.88      inference('sup-', [status(thm)], ['57', '58'])).
% 0.65/0.88  thf('60', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i]:
% 0.65/0.88         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.65/0.88      inference('sup+', [status(thm)], ['56', '59'])).
% 0.65/0.88  thf('61', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i]:
% 0.65/0.88         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.65/0.88      inference('sup+', [status(thm)], ['55', '60'])).
% 0.65/0.88  thf(t32_xboole_1, axiom,
% 0.65/0.88    (![A:$i,B:$i]:
% 0.65/0.88     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.65/0.88       ( ( A ) = ( B ) ) ))).
% 0.65/0.88  thf('62', plain,
% 0.65/0.88      (![X12 : $i, X13 : $i]:
% 0.65/0.88         (((X13) = (X12))
% 0.65/0.88          | ((k4_xboole_0 @ X13 @ X12) != (k4_xboole_0 @ X12 @ X13)))),
% 0.65/0.88      inference('cnf', [status(esa)], [t32_xboole_1])).
% 0.65/0.88  thf('63', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i]:
% 0.65/0.88         (((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.65/0.88          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['61', '62'])).
% 0.65/0.88  thf('64', plain,
% 0.65/0.88      ((((k4_xboole_0 @ sk_B_1 @ sk_D) != (k1_xboole_0))
% 0.65/0.88        | ((sk_B_1) = (k3_xboole_0 @ sk_D @ sk_B_1)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['54', '63'])).
% 0.65/0.88  thf('65', plain, (((sk_D) = (k3_xboole_0 @ sk_D @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['52', '53'])).
% 0.65/0.88  thf('66', plain,
% 0.65/0.88      ((((k4_xboole_0 @ sk_B_1 @ sk_D) != (k1_xboole_0)) | ((sk_B_1) = (sk_D)))),
% 0.65/0.88      inference('demod', [status(thm)], ['64', '65'])).
% 0.65/0.88  thf('67', plain,
% 0.65/0.88      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.65/0.88         ((k2_zfmisc_1 @ (k4_xboole_0 @ X31 @ X33) @ X32)
% 0.65/0.88           = (k4_xboole_0 @ (k2_zfmisc_1 @ X31 @ X32) @ 
% 0.65/0.88              (k2_zfmisc_1 @ X33 @ X32)))),
% 0.65/0.88      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.65/0.88  thf('68', plain,
% 0.65/0.88      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('69', plain,
% 0.65/0.88      (![X31 : $i, X33 : $i, X34 : $i]:
% 0.65/0.88         ((k2_zfmisc_1 @ X34 @ (k4_xboole_0 @ X31 @ X33))
% 0.65/0.88           = (k4_xboole_0 @ (k2_zfmisc_1 @ X34 @ X31) @ 
% 0.65/0.88              (k2_zfmisc_1 @ X34 @ X33)))),
% 0.65/0.88      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.65/0.88  thf('70', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         ((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ X0))
% 0.65/0.88           = (k4_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 0.65/0.88              (k2_zfmisc_1 @ sk_A @ X0)))),
% 0.65/0.88      inference('sup+', [status(thm)], ['68', '69'])).
% 0.65/0.88  thf('71', plain,
% 0.65/0.88      (((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_D))
% 0.65/0.88         = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_C_1 @ sk_A) @ sk_D))),
% 0.65/0.88      inference('sup+', [status(thm)], ['67', '70'])).
% 0.65/0.88  thf('72', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i]:
% 0.65/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.65/0.88      inference('sup-', [status(thm)], ['57', '58'])).
% 0.65/0.88  thf('73', plain,
% 0.65/0.88      (![X17 : $i, X18 : $i]:
% 0.65/0.88         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.65/0.88           = (k3_xboole_0 @ X17 @ X18))),
% 0.65/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.65/0.88  thf('74', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i]:
% 0.65/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 0.65/0.88           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.65/0.88      inference('sup+', [status(thm)], ['72', '73'])).
% 0.65/0.88  thf('75', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.65/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.88  thf('76', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.65/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.65/0.88  thf('77', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i]:
% 0.65/0.88         ((k4_xboole_0 @ X0 @ X1)
% 0.65/0.88           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.65/0.88      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.65/0.88  thf('78', plain,
% 0.65/0.88      (![X19 : $i, X20 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X20)),
% 0.65/0.88      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.65/0.88  thf('79', plain,
% 0.65/0.88      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.65/0.88      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.65/0.88  thf('80', plain,
% 0.65/0.88      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.65/0.88         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.65/0.88          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.65/0.88      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.65/0.88  thf('81', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i]:
% 0.65/0.88         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.65/0.88      inference('sup-', [status(thm)], ['79', '80'])).
% 0.65/0.88  thf('82', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i]:
% 0.65/0.88         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.65/0.88      inference('sup-', [status(thm)], ['78', '81'])).
% 0.65/0.88  thf('83', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.65/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.65/0.88  thf('84', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i]:
% 0.65/0.88         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.65/0.88      inference('demod', [status(thm)], ['82', '83'])).
% 0.65/0.88  thf('85', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         ((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 0.65/0.88           = (k4_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 0.65/0.88              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 0.65/0.88      inference('sup+', [status(thm)], ['1', '2'])).
% 0.65/0.88  thf('86', plain,
% 0.65/0.88      (![X17 : $i, X18 : $i]:
% 0.65/0.88         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.65/0.88           = (k3_xboole_0 @ X17 @ X18))),
% 0.65/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.65/0.88  thf('87', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         ((k4_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 0.65/0.88           (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1))
% 0.65/0.88           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 0.65/0.88              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 0.65/0.88      inference('sup+', [status(thm)], ['85', '86'])).
% 0.65/0.88  thf('88', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         ((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 0.65/0.88           = (k4_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 0.65/0.88              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 0.65/0.88      inference('sup+', [status(thm)], ['1', '2'])).
% 0.65/0.88  thf('89', plain,
% 0.65/0.88      (![X17 : $i, X18 : $i]:
% 0.65/0.88         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.65/0.88           = (k3_xboole_0 @ X17 @ X18))),
% 0.65/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.65/0.88  thf('90', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 0.65/0.88           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 0.65/0.88              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 0.65/0.88      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.65/0.88  thf(t123_zfmisc_1, axiom,
% 0.65/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.88     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.65/0.88       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.65/0.88  thf('91', plain,
% 0.65/0.88      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.65/0.88         ((k2_zfmisc_1 @ (k3_xboole_0 @ X27 @ X29) @ (k3_xboole_0 @ X28 @ X30))
% 0.65/0.88           = (k3_xboole_0 @ (k2_zfmisc_1 @ X27 @ X28) @ 
% 0.65/0.88              (k2_zfmisc_1 @ X29 @ X30)))),
% 0.65/0.88      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.65/0.88  thf('92', plain, (((sk_D) = (k3_xboole_0 @ sk_D @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['52', '53'])).
% 0.65/0.88  thf('93', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 0.65/0.88           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_D))),
% 0.65/0.88      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.65/0.88  thf('94', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         ((k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1)
% 0.65/0.88           = (k2_zfmisc_1 @ 
% 0.65/0.88              (k3_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ X0 @ sk_A)) @ sk_D))),
% 0.65/0.88      inference('sup+', [status(thm)], ['84', '93'])).
% 0.65/0.88  thf('95', plain,
% 0.65/0.88      (![X26 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X26) = (k1_xboole_0))),
% 0.65/0.88      inference('simplify', [status(thm)], ['37'])).
% 0.65/0.88  thf('96', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         ((k1_xboole_0)
% 0.65/0.88           = (k2_zfmisc_1 @ 
% 0.65/0.88              (k3_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ X0 @ sk_A)) @ sk_D))),
% 0.65/0.88      inference('demod', [status(thm)], ['94', '95'])).
% 0.65/0.88  thf('97', plain,
% 0.65/0.88      (((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_C_1 @ sk_A) @ sk_D))),
% 0.65/0.88      inference('sup+', [status(thm)], ['77', '96'])).
% 0.65/0.88  thf('98', plain,
% 0.65/0.88      (((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_D)) = (k1_xboole_0))),
% 0.65/0.88      inference('demod', [status(thm)], ['71', '97'])).
% 0.65/0.88  thf('99', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.65/0.88      inference('demod', [status(thm)], ['16', '17'])).
% 0.65/0.88  thf('100', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 0.65/0.88           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_D))),
% 0.65/0.88      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.65/0.88  thf('101', plain,
% 0.65/0.88      (((k2_zfmisc_1 @ sk_A @ sk_B_1)
% 0.65/0.88         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_D))),
% 0.65/0.88      inference('sup+', [status(thm)], ['99', '100'])).
% 0.65/0.88  thf('102', plain,
% 0.65/0.88      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('103', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.65/0.88      inference('simplify', [status(thm)], ['31'])).
% 0.65/0.88  thf('104', plain,
% 0.65/0.88      (![X17 : $i, X18 : $i]:
% 0.65/0.88         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.65/0.88           = (k3_xboole_0 @ X17 @ X18))),
% 0.65/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.65/0.88  thf('105', plain,
% 0.65/0.88      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.65/0.88      inference('sup+', [status(thm)], ['103', '104'])).
% 0.65/0.88  thf('106', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.65/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.88  thf('107', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.65/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.65/0.88  thf('108', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.65/0.88      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.65/0.88  thf('109', plain,
% 0.65/0.88      (((k2_zfmisc_1 @ sk_C_1 @ sk_D) = (k2_zfmisc_1 @ sk_A @ sk_D))),
% 0.65/0.88      inference('demod', [status(thm)], ['101', '102', '108'])).
% 0.65/0.88  thf('110', plain,
% 0.65/0.88      (((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_C_1 @ sk_A) @ sk_D))),
% 0.65/0.88      inference('sup+', [status(thm)], ['77', '96'])).
% 0.65/0.88  thf('111', plain,
% 0.65/0.88      (![X24 : $i, X25 : $i]:
% 0.65/0.88         (((X24) = (k1_xboole_0))
% 0.65/0.88          | ((X25) = (k1_xboole_0))
% 0.65/0.88          | ((k2_zfmisc_1 @ X25 @ X24) != (k1_xboole_0)))),
% 0.65/0.88      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.65/0.88  thf('112', plain,
% 0.65/0.88      ((((k1_xboole_0) != (k1_xboole_0))
% 0.65/0.88        | ((k4_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))
% 0.65/0.88        | ((sk_D) = (k1_xboole_0)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['110', '111'])).
% 0.65/0.88  thf('113', plain,
% 0.65/0.88      ((((sk_D) = (k1_xboole_0))
% 0.65/0.88        | ((k4_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0)))),
% 0.65/0.88      inference('simplify', [status(thm)], ['112'])).
% 0.65/0.88  thf('114', plain,
% 0.65/0.88      (![X17 : $i, X18 : $i]:
% 0.65/0.88         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.65/0.88           = (k3_xboole_0 @ X17 @ X18))),
% 0.65/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.65/0.88  thf('115', plain,
% 0.65/0.88      ((((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_A))
% 0.65/0.88        | ((sk_D) = (k1_xboole_0)))),
% 0.65/0.88      inference('sup+', [status(thm)], ['113', '114'])).
% 0.65/0.88  thf('116', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.65/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.88  thf('117', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.65/0.88      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.65/0.88  thf('118', plain, ((((sk_C_1) = (sk_A)) | ((sk_D) = (k1_xboole_0)))),
% 0.65/0.88      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.65/0.88  thf('119', plain,
% 0.65/0.88      (![X25 : $i, X26 : $i]:
% 0.65/0.88         (((k2_zfmisc_1 @ X25 @ X26) = (k1_xboole_0))
% 0.65/0.88          | ((X26) != (k1_xboole_0)))),
% 0.65/0.88      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.65/0.88  thf('120', plain,
% 0.65/0.88      (![X25 : $i]: ((k2_zfmisc_1 @ X25 @ k1_xboole_0) = (k1_xboole_0))),
% 0.65/0.88      inference('simplify', [status(thm)], ['119'])).
% 0.65/0.88  thf('121', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (((k2_zfmisc_1 @ X0 @ sk_D) = (k1_xboole_0)) | ((sk_C_1) = (sk_A)))),
% 0.65/0.88      inference('sup+', [status(thm)], ['118', '120'])).
% 0.65/0.88  thf('122', plain,
% 0.65/0.88      ((((k2_zfmisc_1 @ sk_C_1 @ sk_D) = (k1_xboole_0)) | ((sk_C_1) = (sk_A)))),
% 0.65/0.88      inference('sup+', [status(thm)], ['109', '121'])).
% 0.65/0.88  thf('123', plain,
% 0.65/0.88      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('124', plain,
% 0.65/0.88      (![X24 : $i, X25 : $i]:
% 0.65/0.88         (((X24) = (k1_xboole_0))
% 0.65/0.88          | ((X25) = (k1_xboole_0))
% 0.65/0.88          | ((k2_zfmisc_1 @ X25 @ X24) != (k1_xboole_0)))),
% 0.65/0.88      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.65/0.88  thf('125', plain,
% 0.65/0.88      ((((k2_zfmisc_1 @ sk_C_1 @ sk_D) != (k1_xboole_0))
% 0.65/0.88        | ((sk_A) = (k1_xboole_0))
% 0.65/0.88        | ((sk_B_1) = (k1_xboole_0)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['123', '124'])).
% 0.65/0.88  thf('126', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('127', plain, (((sk_A) != (k1_xboole_0))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('128', plain, (((k2_zfmisc_1 @ sk_C_1 @ sk_D) != (k1_xboole_0))),
% 0.65/0.88      inference('simplify_reflect-', [status(thm)], ['125', '126', '127'])).
% 0.65/0.88  thf('129', plain, (((sk_C_1) = (sk_A))),
% 0.65/0.88      inference('simplify_reflect-', [status(thm)], ['122', '128'])).
% 0.65/0.88  thf('130', plain,
% 0.65/0.88      (((k2_zfmisc_1 @ sk_C_1 @ (k4_xboole_0 @ sk_B_1 @ sk_D)) = (k1_xboole_0))),
% 0.65/0.88      inference('demod', [status(thm)], ['98', '129'])).
% 0.65/0.88  thf('131', plain,
% 0.65/0.88      (![X24 : $i, X25 : $i]:
% 0.65/0.88         (((X24) = (k1_xboole_0))
% 0.65/0.88          | ((X25) = (k1_xboole_0))
% 0.65/0.88          | ((k2_zfmisc_1 @ X25 @ X24) != (k1_xboole_0)))),
% 0.65/0.88      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.65/0.88  thf('132', plain,
% 0.65/0.88      ((((k1_xboole_0) != (k1_xboole_0))
% 0.65/0.88        | ((sk_C_1) = (k1_xboole_0))
% 0.65/0.88        | ((k4_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['130', '131'])).
% 0.65/0.88  thf('133', plain,
% 0.65/0.88      ((((k4_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 0.65/0.88        | ((sk_C_1) = (k1_xboole_0)))),
% 0.65/0.88      inference('simplify', [status(thm)], ['132'])).
% 0.65/0.88  thf('134', plain, (((sk_A) != (k1_xboole_0))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('135', plain, (((sk_C_1) = (sk_A))),
% 0.65/0.88      inference('simplify_reflect-', [status(thm)], ['122', '128'])).
% 0.65/0.88  thf('136', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.65/0.88      inference('demod', [status(thm)], ['134', '135'])).
% 0.65/0.88  thf('137', plain, (((k4_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.65/0.88      inference('simplify_reflect-', [status(thm)], ['133', '136'])).
% 0.65/0.88  thf('138', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B_1) = (sk_D)))),
% 0.65/0.88      inference('demod', [status(thm)], ['66', '137'])).
% 0.65/0.88  thf('139', plain, (((sk_B_1) = (sk_D))),
% 0.65/0.88      inference('simplify', [status(thm)], ['138'])).
% 0.65/0.88  thf('140', plain, ((((sk_A) != (sk_C_1)) | ((sk_B_1) != (sk_D)))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('141', plain, ((((sk_B_1) != (sk_D))) <= (~ (((sk_B_1) = (sk_D))))),
% 0.65/0.88      inference('split', [status(esa)], ['140'])).
% 0.65/0.88  thf('142', plain, (((sk_C_1) = (sk_A))),
% 0.65/0.88      inference('simplify_reflect-', [status(thm)], ['122', '128'])).
% 0.65/0.88  thf('143', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 0.65/0.88      inference('split', [status(esa)], ['140'])).
% 0.65/0.88  thf('144', plain, ((((sk_C_1) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['142', '143'])).
% 0.65/0.88  thf('145', plain, ((((sk_A) = (sk_C_1)))),
% 0.65/0.88      inference('simplify', [status(thm)], ['144'])).
% 0.65/0.88  thf('146', plain, (~ (((sk_B_1) = (sk_D))) | ~ (((sk_A) = (sk_C_1)))),
% 0.65/0.88      inference('split', [status(esa)], ['140'])).
% 0.65/0.88  thf('147', plain, (~ (((sk_B_1) = (sk_D)))),
% 0.65/0.88      inference('sat_resolution*', [status(thm)], ['145', '146'])).
% 0.65/0.88  thf('148', plain, (((sk_B_1) != (sk_D))),
% 0.65/0.88      inference('simpl_trail', [status(thm)], ['141', '147'])).
% 0.65/0.88  thf('149', plain, ($false),
% 0.65/0.88      inference('simplify_reflect-', [status(thm)], ['139', '148'])).
% 0.65/0.88  
% 0.65/0.88  % SZS output end Refutation
% 0.65/0.88  
% 0.65/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
