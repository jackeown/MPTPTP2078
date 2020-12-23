%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MqKXC1ZfMe

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:30 EST 2020

% Result     : Theorem 15.33s
% Output     : Refutation 15.33s
% Verified   : 
% Statistics : Number of formulae       :  253 (11591 expanded)
%              Number of leaves         :   29 (3941 expanded)
%              Depth                    :   32
%              Number of atoms          : 2167 (94770 expanded)
%              Number of equality atoms :  190 (7959 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X35 @ X36 )
      | ( r1_xboole_0 @ ( k2_tarski @ X35 @ X37 ) @ X36 )
      | ( r2_hidden @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
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

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('8',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X27 @ X29 ) @ ( k3_xboole_0 @ X28 @ X30 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ ( k1_tarski @ X0 ) ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t96_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k5_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k5_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('43',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k5_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['43','54'])).

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

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('57',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('58',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('66',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('74',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('76',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['72','73','74','75','76'])).

thf('78',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('79',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ( k2_zfmisc_1 @ X34 @ ( k4_xboole_0 @ X31 @ X33 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X31 ) @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('80',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X31 @ X33 ) @ X32 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X31 @ X32 ) @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X27 @ X29 ) @ ( k3_xboole_0 @ X28 @ X30 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X2 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X27 @ X29 ) @ ( k3_xboole_0 @ X28 @ X30 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X2 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('88',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('105',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('107',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('108',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['93','108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('113',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X2 ) @ k1_xboole_0 )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ X2 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['86','110','111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['77','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['93','108','109'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('119',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k5_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['72','73','74','75','76'])).

thf('126',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X27 @ X29 ) @ ( k3_xboole_0 @ X28 @ X30 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ k1_xboole_0 @ X2 ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X27 @ X29 ) @ ( k3_xboole_0 @ X28 @ X30 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ k1_xboole_0 @ X2 ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ k1_xboole_0 @ X2 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['93','108','109'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['132','133','134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['125','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['93','108','109'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['137','140','141'])).

thf('143',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X31 @ X33 ) @ X32 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X31 @ X32 ) @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('146',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','40'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('150',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) )
    = ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['148','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('156',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('160',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['154','157','158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['147','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['144','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('164',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['162','167'])).

thf('169',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X27 @ X29 ) @ ( k3_xboole_0 @ X28 @ X30 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('171',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('173',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('174',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('175',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['172','178'])).

thf('180',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('183',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('186',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('189',plain,
    ( ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['168','171','181','182','183','184','185','186','187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['137','140','141'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['137','140','141'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X1 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['189','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','117','124','193'])).

thf('195',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ ( k1_tarski @ X0 ) ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ ( k1_tarski @ X0 ) ) @ ( k2_zfmisc_1 @ X3 @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf(t131_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( A != B )
     => ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) )
        & ( r1_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( A != B )
       => ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) )
          & ( r1_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t131_zfmisc_1])).

thf('197',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ) ) ),
    inference(split,[status(esa)],['197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('200',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('201',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r2_hidden @ X2 @ X3 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['189','192'])).

thf('203',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X2 @ X3 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) )
      | ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['197'])).

thf('206',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('208',plain,(
    ! [X18: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X20 )
      | ( X22 = X21 )
      | ( X22 = X18 )
      | ( X20
       != ( k2_tarski @ X21 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('209',plain,(
    ! [X18: $i,X21: $i,X22: $i] :
      ( ( X22 = X18 )
      | ( X22 = X21 )
      | ~ ( r2_hidden @ X22 @ ( k2_tarski @ X21 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['207','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,
    ( ( sk_A = sk_B )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['206','211'])).

thf('213',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['212','213'])).

thf('215',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['197'])).

thf('216',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['214','215'])).

thf('217',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['198','216'])).

thf('218',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['196','217'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('220',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['220','221'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MqKXC1ZfMe
% 0.16/0.37  % Computer   : n015.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 13:39:38 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 15.33/15.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 15.33/15.51  % Solved by: fo/fo7.sh
% 15.33/15.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.33/15.51  % done 9975 iterations in 15.019s
% 15.33/15.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 15.33/15.51  % SZS output start Refutation
% 15.33/15.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 15.33/15.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 15.33/15.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 15.33/15.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.33/15.51  thf(sk_A_type, type, sk_A: $i).
% 15.33/15.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 15.33/15.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.33/15.51  thf(sk_B_type, type, sk_B: $i).
% 15.33/15.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 15.33/15.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 15.33/15.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 15.33/15.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 15.33/15.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 15.33/15.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 15.33/15.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 15.33/15.51  thf(t69_enumset1, axiom,
% 15.33/15.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 15.33/15.51  thf('0', plain, (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 15.33/15.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 15.33/15.51  thf(t57_zfmisc_1, axiom,
% 15.33/15.51    (![A:$i,B:$i,C:$i]:
% 15.33/15.51     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 15.33/15.51          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 15.33/15.51  thf('1', plain,
% 15.33/15.51      (![X35 : $i, X36 : $i, X37 : $i]:
% 15.33/15.51         ((r2_hidden @ X35 @ X36)
% 15.33/15.51          | (r1_xboole_0 @ (k2_tarski @ X35 @ X37) @ X36)
% 15.33/15.51          | (r2_hidden @ X37 @ X36))),
% 15.33/15.51      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 15.33/15.51  thf('2', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 15.33/15.51          | (r2_hidden @ X0 @ X1)
% 15.33/15.51          | (r2_hidden @ X0 @ X1))),
% 15.33/15.51      inference('sup+', [status(thm)], ['0', '1'])).
% 15.33/15.51  thf('3', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 15.33/15.51      inference('simplify', [status(thm)], ['2'])).
% 15.33/15.51  thf(d7_xboole_0, axiom,
% 15.33/15.51    (![A:$i,B:$i]:
% 15.33/15.51     ( ( r1_xboole_0 @ A @ B ) <=>
% 15.33/15.51       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 15.33/15.51  thf('4', plain,
% 15.33/15.51      (![X2 : $i, X3 : $i]:
% 15.33/15.51         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 15.33/15.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 15.33/15.51  thf('5', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((r2_hidden @ X1 @ X0)
% 15.33/15.51          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 15.33/15.51      inference('sup-', [status(thm)], ['3', '4'])).
% 15.33/15.51  thf(commutativity_k3_xboole_0, axiom,
% 15.33/15.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 15.33/15.51  thf('6', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.33/15.51  thf('7', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         (((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 15.33/15.51          | (r2_hidden @ X0 @ X1))),
% 15.33/15.51      inference('sup+', [status(thm)], ['5', '6'])).
% 15.33/15.51  thf(t123_zfmisc_1, axiom,
% 15.33/15.51    (![A:$i,B:$i,C:$i,D:$i]:
% 15.33/15.51     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 15.33/15.51       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 15.33/15.51  thf('8', plain,
% 15.33/15.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k3_xboole_0 @ X27 @ X29) @ (k3_xboole_0 @ X28 @ X30))
% 15.33/15.51           = (k3_xboole_0 @ (k2_zfmisc_1 @ X27 @ X28) @ 
% 15.33/15.51              (k2_zfmisc_1 @ X29 @ X30)))),
% 15.33/15.51      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 15.33/15.51  thf('9', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.33/15.51  thf('10', plain,
% 15.33/15.51      (![X2 : $i, X4 : $i]:
% 15.33/15.51         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 15.33/15.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 15.33/15.51  thf('11', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('sup-', [status(thm)], ['9', '10'])).
% 15.33/15.51  thf('12', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.33/15.51         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 15.33/15.51            != (k1_xboole_0))
% 15.33/15.51          | (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1)))),
% 15.33/15.51      inference('sup-', [status(thm)], ['8', '11'])).
% 15.33/15.51  thf('13', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.33/15.51         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ k1_xboole_0)
% 15.33/15.51            != (k1_xboole_0))
% 15.33/15.51          | (r2_hidden @ X0 @ X1)
% 15.33/15.51          | (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ (k1_tarski @ X0)) @ 
% 15.33/15.51             (k2_zfmisc_1 @ X3 @ X1)))),
% 15.33/15.51      inference('sup-', [status(thm)], ['7', '12'])).
% 15.33/15.51  thf(t3_boole, axiom,
% 15.33/15.51    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 15.33/15.51  thf('14', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_boole])).
% 15.33/15.51  thf(t100_xboole_1, axiom,
% 15.33/15.51    (![A:$i,B:$i]:
% 15.33/15.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 15.33/15.51  thf('15', plain,
% 15.33/15.51      (![X11 : $i, X12 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ X11 @ X12)
% 15.33/15.51           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 15.33/15.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 15.33/15.51  thf(t96_xboole_1, axiom,
% 15.33/15.51    (![A:$i,B:$i]:
% 15.33/15.51     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 15.33/15.51  thf('16', plain,
% 15.33/15.51      (![X16 : $i, X17 : $i]:
% 15.33/15.51         (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ (k5_xboole_0 @ X16 @ X17))),
% 15.33/15.51      inference('cnf', [status(esa)], [t96_xboole_1])).
% 15.33/15.51  thf('17', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         (r1_tarski @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.33/15.51          (k4_xboole_0 @ X1 @ X0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['15', '16'])).
% 15.33/15.51  thf('18', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         (r1_tarski @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 15.33/15.51          X0)),
% 15.33/15.51      inference('sup+', [status(thm)], ['14', '17'])).
% 15.33/15.51  thf(t28_xboole_1, axiom,
% 15.33/15.51    (![A:$i,B:$i]:
% 15.33/15.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 15.33/15.51  thf('19', plain,
% 15.33/15.51      (![X13 : $i, X14 : $i]:
% 15.33/15.51         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 15.33/15.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 15.33/15.51  thf('20', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ 
% 15.33/15.51           (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)) @ X0)
% 15.33/15.51           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 15.33/15.51      inference('sup-', [status(thm)], ['18', '19'])).
% 15.33/15.51  thf('21', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.33/15.51  thf('22', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ X0 @ 
% 15.33/15.51           (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))
% 15.33/15.51           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 15.33/15.51      inference('demod', [status(thm)], ['20', '21'])).
% 15.33/15.51  thf('23', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_boole])).
% 15.33/15.51  thf('24', plain,
% 15.33/15.51      (![X11 : $i, X12 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ X11 @ X12)
% 15.33/15.51           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 15.33/15.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 15.33/15.51  thf(l97_xboole_1, axiom,
% 15.33/15.51    (![A:$i,B:$i]:
% 15.33/15.51     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 15.33/15.51  thf('25', plain,
% 15.33/15.51      (![X9 : $i, X10 : $i]:
% 15.33/15.51         (r1_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k5_xboole_0 @ X9 @ X10))),
% 15.33/15.51      inference('cnf', [status(esa)], [l97_xboole_1])).
% 15.33/15.51  thf('26', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.33/15.51          (k4_xboole_0 @ X1 @ X0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['24', '25'])).
% 15.33/15.51  thf('27', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         (r1_xboole_0 @ 
% 15.33/15.51          (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)) @ X0)),
% 15.33/15.51      inference('sup+', [status(thm)], ['23', '26'])).
% 15.33/15.51  thf('28', plain,
% 15.33/15.51      (![X2 : $i, X3 : $i]:
% 15.33/15.51         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 15.33/15.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 15.33/15.51  thf('29', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ 
% 15.33/15.51           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)) @ X0)
% 15.33/15.51           = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['27', '28'])).
% 15.33/15.51  thf('30', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.33/15.51  thf('31', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ X0 @ 
% 15.33/15.51           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))
% 15.33/15.51           = (k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['29', '30'])).
% 15.33/15.51  thf('32', plain,
% 15.33/15.51      (![X9 : $i, X10 : $i]:
% 15.33/15.51         (r1_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k5_xboole_0 @ X9 @ X10))),
% 15.33/15.51      inference('cnf', [status(esa)], [l97_xboole_1])).
% 15.33/15.51  thf('33', plain,
% 15.33/15.51      (![X2 : $i, X3 : $i]:
% 15.33/15.51         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 15.33/15.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 15.33/15.51  thf('34', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 15.33/15.51           = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['32', '33'])).
% 15.33/15.51  thf('35', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.33/15.51  thf('36', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 15.33/15.51           = (k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['34', '35'])).
% 15.33/15.51  thf('37', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ 
% 15.33/15.51           (k5_xboole_0 @ X0 @ 
% 15.33/15.51            (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))) @ 
% 15.33/15.51           k1_xboole_0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['31', '36'])).
% 15.33/15.51  thf('38', plain,
% 15.33/15.51      (![X11 : $i, X12 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ X11 @ X12)
% 15.33/15.51           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 15.33/15.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 15.33/15.51  thf('39', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.33/15.51  thf('40', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ k1_xboole_0 @ 
% 15.33/15.51           (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))
% 15.33/15.51           = (k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['37', '38', '39'])).
% 15.33/15.51  thf('41', plain,
% 15.33/15.51      (((k4_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 15.33/15.51         = (k1_xboole_0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['22', '40'])).
% 15.33/15.51  thf('42', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.33/15.51          (k4_xboole_0 @ X1 @ X0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['24', '25'])).
% 15.33/15.51  thf('43', plain,
% 15.33/15.51      ((r1_xboole_0 @ 
% 15.33/15.51        (k3_xboole_0 @ k1_xboole_0 @ 
% 15.33/15.51         (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))) @ 
% 15.33/15.51        k1_xboole_0)),
% 15.33/15.51      inference('sup+', [status(thm)], ['41', '42'])).
% 15.33/15.51  thf('44', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_boole])).
% 15.33/15.51  thf('45', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.33/15.51  thf('46', plain,
% 15.33/15.51      (![X11 : $i, X12 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ X11 @ X12)
% 15.33/15.51           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 15.33/15.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 15.33/15.51  thf('47', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ X0 @ X1)
% 15.33/15.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 15.33/15.51      inference('sup+', [status(thm)], ['45', '46'])).
% 15.33/15.51  thf('48', plain,
% 15.33/15.51      (![X9 : $i, X10 : $i]:
% 15.33/15.51         (r1_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k5_xboole_0 @ X9 @ X10))),
% 15.33/15.51      inference('cnf', [status(esa)], [l97_xboole_1])).
% 15.33/15.51  thf('49', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 15.33/15.51          (k4_xboole_0 @ X1 @ X0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['47', '48'])).
% 15.33/15.51  thf('50', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         (r1_xboole_0 @ 
% 15.33/15.51          (k3_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)) @ X0)),
% 15.33/15.51      inference('sup+', [status(thm)], ['44', '49'])).
% 15.33/15.51  thf('51', plain,
% 15.33/15.51      (![X2 : $i, X3 : $i]:
% 15.33/15.51         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 15.33/15.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 15.33/15.51  thf('52', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ 
% 15.33/15.51           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)) @ X0)
% 15.33/15.51           = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['50', '51'])).
% 15.33/15.51  thf('53', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.33/15.51  thf('54', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ X0 @ 
% 15.33/15.51           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))
% 15.33/15.51           = (k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['52', '53'])).
% 15.33/15.51  thf('55', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 15.33/15.51      inference('demod', [status(thm)], ['43', '54'])).
% 15.33/15.51  thf(t3_xboole_0, axiom,
% 15.33/15.51    (![A:$i,B:$i]:
% 15.33/15.51     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 15.33/15.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 15.33/15.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 15.33/15.51            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 15.33/15.51  thf('56', plain,
% 15.33/15.51      (![X5 : $i, X6 : $i]:
% 15.33/15.51         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 15.33/15.51  thf('57', plain,
% 15.33/15.51      (![X5 : $i, X6 : $i]:
% 15.33/15.51         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 15.33/15.51  thf('58', plain,
% 15.33/15.51      (![X5 : $i, X7 : $i, X8 : $i]:
% 15.33/15.51         (~ (r2_hidden @ X7 @ X5)
% 15.33/15.51          | ~ (r2_hidden @ X7 @ X8)
% 15.33/15.51          | ~ (r1_xboole_0 @ X5 @ X8))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 15.33/15.51  thf('59', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.33/15.51         ((r1_xboole_0 @ X0 @ X1)
% 15.33/15.51          | ~ (r1_xboole_0 @ X0 @ X2)
% 15.33/15.51          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 15.33/15.51      inference('sup-', [status(thm)], ['57', '58'])).
% 15.33/15.51  thf('60', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((r1_xboole_0 @ X0 @ X1)
% 15.33/15.51          | ~ (r1_xboole_0 @ X0 @ X0)
% 15.33/15.51          | (r1_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('sup-', [status(thm)], ['56', '59'])).
% 15.33/15.51  thf('61', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('simplify', [status(thm)], ['60'])).
% 15.33/15.51  thf('62', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 15.33/15.51      inference('sup-', [status(thm)], ['55', '61'])).
% 15.33/15.51  thf('63', plain,
% 15.33/15.51      (![X2 : $i, X3 : $i]:
% 15.33/15.51         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 15.33/15.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 15.33/15.51  thf('64', plain,
% 15.33/15.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['62', '63'])).
% 15.33/15.51  thf('65', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ X0 @ X1)
% 15.33/15.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 15.33/15.51      inference('sup+', [status(thm)], ['45', '46'])).
% 15.33/15.51  thf('66', plain,
% 15.33/15.51      (![X16 : $i, X17 : $i]:
% 15.33/15.51         (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ (k5_xboole_0 @ X16 @ X17))),
% 15.33/15.51      inference('cnf', [status(esa)], [t96_xboole_1])).
% 15.33/15.51  thf('67', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         (r1_tarski @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 15.33/15.51          (k4_xboole_0 @ X1 @ X0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['65', '66'])).
% 15.33/15.51  thf('68', plain,
% 15.33/15.51      (![X13 : $i, X14 : $i]:
% 15.33/15.51         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 15.33/15.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 15.33/15.51  thf('69', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 15.33/15.51           (k4_xboole_0 @ X1 @ X0))
% 15.33/15.51           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 15.33/15.51      inference('sup-', [status(thm)], ['67', '68'])).
% 15.33/15.51  thf('70', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.33/15.51  thf('71', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 15.33/15.51           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))
% 15.33/15.51           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 15.33/15.51      inference('demod', [status(thm)], ['69', '70'])).
% 15.33/15.51  thf('72', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ 
% 15.33/15.51           (k4_xboole_0 @ X0 @ k1_xboole_0))
% 15.33/15.51           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 15.33/15.51      inference('sup+', [status(thm)], ['64', '71'])).
% 15.33/15.51  thf('73', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_boole])).
% 15.33/15.51  thf('74', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_boole])).
% 15.33/15.51  thf('75', plain,
% 15.33/15.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['62', '63'])).
% 15.33/15.51  thf('76', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_boole])).
% 15.33/15.51  thf('77', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 15.33/15.51      inference('demod', [status(thm)], ['72', '73', '74', '75', '76'])).
% 15.33/15.51  thf('78', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_boole])).
% 15.33/15.51  thf(t125_zfmisc_1, axiom,
% 15.33/15.51    (![A:$i,B:$i,C:$i]:
% 15.33/15.51     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 15.33/15.51         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 15.33/15.51       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 15.33/15.51         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 15.33/15.51  thf('79', plain,
% 15.33/15.51      (![X31 : $i, X33 : $i, X34 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ X34 @ (k4_xboole_0 @ X31 @ X33))
% 15.33/15.51           = (k4_xboole_0 @ (k2_zfmisc_1 @ X34 @ X31) @ 
% 15.33/15.51              (k2_zfmisc_1 @ X34 @ X33)))),
% 15.33/15.51      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 15.33/15.51  thf('80', plain,
% 15.33/15.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k4_xboole_0 @ X31 @ X33) @ X32)
% 15.33/15.51           = (k4_xboole_0 @ (k2_zfmisc_1 @ X31 @ X32) @ 
% 15.33/15.51              (k2_zfmisc_1 @ X33 @ X32)))),
% 15.33/15.51      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 15.33/15.51  thf('81', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 15.33/15.51           = (k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 15.33/15.51      inference('sup+', [status(thm)], ['79', '80'])).
% 15.33/15.51  thf('82', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k4_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 15.33/15.51           = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['78', '81'])).
% 15.33/15.51  thf('83', plain,
% 15.33/15.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k3_xboole_0 @ X27 @ X29) @ (k3_xboole_0 @ X28 @ X30))
% 15.33/15.51           = (k3_xboole_0 @ (k2_zfmisc_1 @ X27 @ X28) @ 
% 15.33/15.51              (k2_zfmisc_1 @ X29 @ X30)))),
% 15.33/15.51      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 15.33/15.51  thf('84', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X2) @ 
% 15.33/15.51           (k3_xboole_0 @ k1_xboole_0 @ X1))
% 15.33/15.51           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0) @ 
% 15.33/15.51              (k2_zfmisc_1 @ X2 @ X1)))),
% 15.33/15.51      inference('sup+', [status(thm)], ['82', '83'])).
% 15.33/15.51  thf('85', plain,
% 15.33/15.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k3_xboole_0 @ X27 @ X29) @ (k3_xboole_0 @ X28 @ X30))
% 15.33/15.51           = (k3_xboole_0 @ (k2_zfmisc_1 @ X27 @ X28) @ 
% 15.33/15.51              (k2_zfmisc_1 @ X29 @ X30)))),
% 15.33/15.51      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 15.33/15.51  thf('86', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X2) @ 
% 15.33/15.51           (k3_xboole_0 @ k1_xboole_0 @ X1))
% 15.33/15.51           = (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ X2) @ 
% 15.33/15.51              (k3_xboole_0 @ k1_xboole_0 @ X1)))),
% 15.33/15.51      inference('demod', [status(thm)], ['84', '85'])).
% 15.33/15.51  thf('87', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_boole])).
% 15.33/15.51  thf('88', plain,
% 15.33/15.51      (![X16 : $i, X17 : $i]:
% 15.33/15.51         (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ (k5_xboole_0 @ X16 @ X17))),
% 15.33/15.51      inference('cnf', [status(esa)], [t96_xboole_1])).
% 15.33/15.51  thf('89', plain,
% 15.33/15.51      (![X0 : $i]: (r1_tarski @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['87', '88'])).
% 15.33/15.51  thf('90', plain,
% 15.33/15.51      (![X13 : $i, X14 : $i]:
% 15.33/15.51         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 15.33/15.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 15.33/15.51  thf('91', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['89', '90'])).
% 15.33/15.51  thf('92', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ X0 @ X1)
% 15.33/15.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 15.33/15.51      inference('sup+', [status(thm)], ['45', '46'])).
% 15.33/15.51  thf('93', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 15.33/15.51           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['91', '92'])).
% 15.33/15.51  thf('94', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ X0 @ 
% 15.33/15.51           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))
% 15.33/15.51           = (k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['52', '53'])).
% 15.33/15.51  thf('95', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 15.33/15.51           = (k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['34', '35'])).
% 15.33/15.51  thf('96', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ 
% 15.33/15.51           (k5_xboole_0 @ X0 @ 
% 15.33/15.51            (k3_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))) @ 
% 15.33/15.51           k1_xboole_0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['94', '95'])).
% 15.33/15.51  thf('97', plain,
% 15.33/15.51      (![X11 : $i, X12 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ X11 @ X12)
% 15.33/15.51           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 15.33/15.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 15.33/15.51  thf('98', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.33/15.51  thf('99', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ k1_xboole_0 @ 
% 15.33/15.51           (k4_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))
% 15.33/15.51           = (k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['96', '97', '98'])).
% 15.33/15.51  thf('100', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ X0 @ X1)
% 15.33/15.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 15.33/15.51      inference('sup+', [status(thm)], ['45', '46'])).
% 15.33/15.51  thf('101', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ 
% 15.33/15.51           (k4_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)) @ k1_xboole_0)
% 15.33/15.51           = (k5_xboole_0 @ 
% 15.33/15.51              (k4_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 15.33/15.51              k1_xboole_0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['99', '100'])).
% 15.33/15.51  thf('102', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_boole])).
% 15.33/15.51  thf('103', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 15.33/15.51           = (k5_xboole_0 @ 
% 15.33/15.51              (k4_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 15.33/15.51              k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['101', '102'])).
% 15.33/15.51  thf('104', plain,
% 15.33/15.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['62', '63'])).
% 15.33/15.51  thf('105', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_boole])).
% 15.33/15.51  thf('106', plain,
% 15.33/15.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['62', '63'])).
% 15.33/15.51  thf('107', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_boole])).
% 15.33/15.51  thf('108', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 15.33/15.51  thf('109', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 15.33/15.51  thf('110', plain,
% 15.33/15.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 15.33/15.51      inference('demod', [status(thm)], ['93', '108', '109'])).
% 15.33/15.51  thf('111', plain,
% 15.33/15.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['62', '63'])).
% 15.33/15.51  thf('112', plain,
% 15.33/15.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['62', '63'])).
% 15.33/15.51  thf('113', plain,
% 15.33/15.51      (![X0 : $i, X2 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X2) @ 
% 15.33/15.51           k1_xboole_0) = (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ X2) @ k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['86', '110', '111', '112'])).
% 15.33/15.51  thf('114', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 15.33/15.51           = (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) @ 
% 15.33/15.51              k1_xboole_0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['77', '113'])).
% 15.33/15.51  thf('115', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k4_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 15.33/15.51           = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['78', '81'])).
% 15.33/15.51  thf('116', plain,
% 15.33/15.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 15.33/15.51      inference('demod', [status(thm)], ['93', '108', '109'])).
% 15.33/15.51  thf('117', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 15.33/15.51           = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['115', '116'])).
% 15.33/15.51  thf('118', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['89', '90'])).
% 15.33/15.51  thf('119', plain,
% 15.33/15.51      (![X9 : $i, X10 : $i]:
% 15.33/15.51         (r1_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k5_xboole_0 @ X9 @ X10))),
% 15.33/15.51      inference('cnf', [status(esa)], [l97_xboole_1])).
% 15.33/15.51  thf('120', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         (r1_xboole_0 @ X0 @ 
% 15.33/15.51          (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 15.33/15.51      inference('sup+', [status(thm)], ['118', '119'])).
% 15.33/15.51  thf('121', plain,
% 15.33/15.51      (![X2 : $i, X3 : $i]:
% 15.33/15.51         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 15.33/15.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 15.33/15.51  thf('122', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ X0 @ 
% 15.33/15.51           (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))
% 15.33/15.51           = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['120', '121'])).
% 15.33/15.51  thf('123', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 15.33/15.51  thf('124', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['122', '123'])).
% 15.33/15.51  thf('125', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 15.33/15.51      inference('demod', [status(thm)], ['72', '73', '74', '75', '76'])).
% 15.33/15.51  thf('126', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_boole])).
% 15.33/15.51  thf('127', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 15.33/15.51           = (k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 15.33/15.51      inference('sup+', [status(thm)], ['79', '80'])).
% 15.33/15.51  thf('128', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 15.33/15.51           = (k2_zfmisc_1 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 15.33/15.51      inference('sup+', [status(thm)], ['126', '127'])).
% 15.33/15.51  thf('129', plain,
% 15.33/15.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k3_xboole_0 @ X27 @ X29) @ (k3_xboole_0 @ X28 @ X30))
% 15.33/15.51           = (k3_xboole_0 @ (k2_zfmisc_1 @ X27 @ X28) @ 
% 15.33/15.51              (k2_zfmisc_1 @ X29 @ X30)))),
% 15.33/15.51      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 15.33/15.51  thf('130', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k3_xboole_0 @ k1_xboole_0 @ X2) @ 
% 15.33/15.51           (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))
% 15.33/15.51           = (k3_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ 
% 15.33/15.51              (k2_zfmisc_1 @ X2 @ X1)))),
% 15.33/15.51      inference('sup+', [status(thm)], ['128', '129'])).
% 15.33/15.51  thf('131', plain,
% 15.33/15.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k3_xboole_0 @ X27 @ X29) @ (k3_xboole_0 @ X28 @ X30))
% 15.33/15.51           = (k3_xboole_0 @ (k2_zfmisc_1 @ X27 @ X28) @ 
% 15.33/15.51              (k2_zfmisc_1 @ X29 @ X30)))),
% 15.33/15.51      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 15.33/15.51  thf('132', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k3_xboole_0 @ k1_xboole_0 @ X2) @ 
% 15.33/15.51           (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))
% 15.33/15.51           = (k2_zfmisc_1 @ (k3_xboole_0 @ k1_xboole_0 @ X2) @ 
% 15.33/15.51              (k3_xboole_0 @ X0 @ X1)))),
% 15.33/15.51      inference('demod', [status(thm)], ['130', '131'])).
% 15.33/15.51  thf('133', plain,
% 15.33/15.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['62', '63'])).
% 15.33/15.51  thf('134', plain,
% 15.33/15.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 15.33/15.51      inference('demod', [status(thm)], ['93', '108', '109'])).
% 15.33/15.51  thf('135', plain,
% 15.33/15.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['62', '63'])).
% 15.33/15.51  thf('136', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ k1_xboole_0 @ 
% 15.33/15.51           (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))
% 15.33/15.51           = (k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X1)))),
% 15.33/15.51      inference('demod', [status(thm)], ['132', '133', '134', '135'])).
% 15.33/15.51  thf('137', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))
% 15.33/15.51           = (k2_zfmisc_1 @ k1_xboole_0 @ 
% 15.33/15.51              (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))))),
% 15.33/15.51      inference('sup+', [status(thm)], ['125', '136'])).
% 15.33/15.51  thf('138', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 15.33/15.51           = (k2_zfmisc_1 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 15.33/15.51      inference('sup+', [status(thm)], ['126', '127'])).
% 15.33/15.51  thf('139', plain,
% 15.33/15.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 15.33/15.51      inference('demod', [status(thm)], ['93', '108', '109'])).
% 15.33/15.51  thf('140', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 15.33/15.51           = (k2_zfmisc_1 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)))),
% 15.33/15.51      inference('demod', [status(thm)], ['138', '139'])).
% 15.33/15.51  thf('141', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['122', '123'])).
% 15.33/15.51  thf('142', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 15.33/15.51           = (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['137', '140', '141'])).
% 15.33/15.51  thf('143', plain,
% 15.33/15.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k4_xboole_0 @ X31 @ X33) @ X32)
% 15.33/15.51           = (k4_xboole_0 @ (k2_zfmisc_1 @ X31 @ X32) @ 
% 15.33/15.51              (k2_zfmisc_1 @ X33 @ X32)))),
% 15.33/15.51      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 15.33/15.51  thf('144', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k4_xboole_0 @ k1_xboole_0 @ X1) @ k1_xboole_0)
% 15.33/15.51           = (k4_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ 
% 15.33/15.51              (k2_zfmisc_1 @ X1 @ k1_xboole_0)))),
% 15.33/15.51      inference('sup+', [status(thm)], ['142', '143'])).
% 15.33/15.51  thf('145', plain,
% 15.33/15.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['62', '63'])).
% 15.33/15.51  thf('146', plain,
% 15.33/15.51      (![X11 : $i, X12 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ X11 @ X12)
% 15.33/15.51           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 15.33/15.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 15.33/15.51  thf('147', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 15.33/15.51           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['145', '146'])).
% 15.33/15.51  thf('148', plain,
% 15.33/15.51      (((k4_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 15.33/15.51         = (k1_xboole_0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['22', '40'])).
% 15.33/15.51  thf('149', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         (r1_tarski @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.33/15.51          (k4_xboole_0 @ X1 @ X0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['15', '16'])).
% 15.33/15.51  thf('150', plain,
% 15.33/15.51      (![X13 : $i, X14 : $i]:
% 15.33/15.51         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 15.33/15.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 15.33/15.51  thf('151', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.33/15.51           (k4_xboole_0 @ X1 @ X0))
% 15.33/15.51           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 15.33/15.51      inference('sup-', [status(thm)], ['149', '150'])).
% 15.33/15.51  thf('152', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.33/15.51  thf('153', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 15.33/15.51           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 15.33/15.51           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 15.33/15.51      inference('demod', [status(thm)], ['151', '152'])).
% 15.33/15.51  thf('154', plain,
% 15.33/15.51      (((k3_xboole_0 @ k1_xboole_0 @ 
% 15.33/15.51         (k4_xboole_0 @ k1_xboole_0 @ 
% 15.33/15.51          (k3_xboole_0 @ k1_xboole_0 @ 
% 15.33/15.51           (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))))
% 15.33/15.51         = (k4_xboole_0 @ k1_xboole_0 @ 
% 15.33/15.51            (k3_xboole_0 @ k1_xboole_0 @ 
% 15.33/15.51             (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))))),
% 15.33/15.51      inference('sup+', [status(thm)], ['148', '153'])).
% 15.33/15.51  thf('155', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ X0 @ 
% 15.33/15.51           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))
% 15.33/15.51           = (k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['52', '53'])).
% 15.33/15.51  thf('156', plain,
% 15.33/15.51      (![X11 : $i, X12 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ X11 @ X12)
% 15.33/15.51           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 15.33/15.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 15.33/15.51  thf('157', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ X0 @ 
% 15.33/15.51           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))
% 15.33/15.51           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['155', '156'])).
% 15.33/15.51  thf('158', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['89', '90'])).
% 15.33/15.51  thf('159', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k4_xboole_0 @ X0 @ 
% 15.33/15.51           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))
% 15.33/15.51           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['155', '156'])).
% 15.33/15.51  thf('160', plain,
% 15.33/15.51      (((k1_xboole_0) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['154', '157', '158', '159'])).
% 15.33/15.51  thf('161', plain,
% 15.33/15.51      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['147', '160'])).
% 15.33/15.51  thf('162', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)
% 15.33/15.51           = (k4_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ 
% 15.33/15.51              (k2_zfmisc_1 @ X1 @ k1_xboole_0)))),
% 15.33/15.51      inference('demod', [status(thm)], ['144', '161'])).
% 15.33/15.51  thf('163', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.33/15.51          (k4_xboole_0 @ X1 @ X0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['24', '25'])).
% 15.33/15.51  thf('164', plain,
% 15.33/15.51      (![X2 : $i, X3 : $i]:
% 15.33/15.51         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 15.33/15.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 15.33/15.51  thf('165', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.33/15.51           (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['163', '164'])).
% 15.33/15.51  thf('166', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.33/15.51  thf('167', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 15.33/15.51           (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))) = (k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['165', '166'])).
% 15.33/15.51  thf('168', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0) @ 
% 15.33/15.51           (k3_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ 
% 15.33/15.51            (k3_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ 
% 15.33/15.51             (k2_zfmisc_1 @ X0 @ k1_xboole_0))))
% 15.33/15.51           = (k1_xboole_0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['162', '167'])).
% 15.33/15.51  thf('169', plain,
% 15.33/15.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ (k3_xboole_0 @ X27 @ X29) @ (k3_xboole_0 @ X28 @ X30))
% 15.33/15.51           = (k3_xboole_0 @ (k2_zfmisc_1 @ X27 @ X28) @ 
% 15.33/15.51              (k2_zfmisc_1 @ X29 @ X30)))),
% 15.33/15.51      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 15.33/15.51  thf('170', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.33/15.51  thf('171', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1))
% 15.33/15.51           = (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 15.33/15.51      inference('sup+', [status(thm)], ['169', '170'])).
% 15.33/15.51  thf('172', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 15.33/15.51      inference('sup-', [status(thm)], ['55', '61'])).
% 15.33/15.51  thf('173', plain,
% 15.33/15.51      (![X5 : $i, X6 : $i]:
% 15.33/15.51         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 15.33/15.51  thf('174', plain,
% 15.33/15.51      (![X5 : $i, X6 : $i]:
% 15.33/15.51         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X6))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 15.33/15.51  thf('175', plain,
% 15.33/15.51      (![X5 : $i, X7 : $i, X8 : $i]:
% 15.33/15.51         (~ (r2_hidden @ X7 @ X5)
% 15.33/15.51          | ~ (r2_hidden @ X7 @ X8)
% 15.33/15.51          | ~ (r1_xboole_0 @ X5 @ X8))),
% 15.33/15.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 15.33/15.51  thf('176', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.33/15.51         ((r1_xboole_0 @ X1 @ X0)
% 15.33/15.51          | ~ (r1_xboole_0 @ X0 @ X2)
% 15.33/15.51          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 15.33/15.51      inference('sup-', [status(thm)], ['174', '175'])).
% 15.33/15.51  thf('177', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((r1_xboole_0 @ X0 @ X1)
% 15.33/15.51          | ~ (r1_xboole_0 @ X1 @ X0)
% 15.33/15.51          | (r1_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('sup-', [status(thm)], ['173', '176'])).
% 15.33/15.51  thf('178', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 15.33/15.51      inference('simplify', [status(thm)], ['177'])).
% 15.33/15.51  thf('179', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 15.33/15.51      inference('sup-', [status(thm)], ['172', '178'])).
% 15.33/15.51  thf('180', plain,
% 15.33/15.51      (![X2 : $i, X3 : $i]:
% 15.33/15.51         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 15.33/15.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 15.33/15.51  thf('181', plain,
% 15.33/15.51      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['179', '180'])).
% 15.33/15.51  thf('182', plain,
% 15.33/15.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['62', '63'])).
% 15.33/15.51  thf('183', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1))
% 15.33/15.51           = (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 15.33/15.51      inference('sup+', [status(thm)], ['169', '170'])).
% 15.33/15.51  thf('184', plain,
% 15.33/15.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['62', '63'])).
% 15.33/15.51  thf('185', plain,
% 15.33/15.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['62', '63'])).
% 15.33/15.51  thf('186', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.33/15.51         ((k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1))
% 15.33/15.51           = (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 15.33/15.51      inference('sup+', [status(thm)], ['169', '170'])).
% 15.33/15.51  thf('187', plain,
% 15.33/15.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['62', '63'])).
% 15.33/15.51  thf('188', plain,
% 15.33/15.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.33/15.51      inference('sup-', [status(thm)], ['62', '63'])).
% 15.33/15.51  thf('189', plain,
% 15.33/15.51      (((k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)],
% 15.33/15.51                ['168', '171', '181', '182', '183', '184', '185', '186', 
% 15.33/15.51                 '187', '188'])).
% 15.33/15.51  thf('190', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 15.33/15.51           = (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['137', '140', '141'])).
% 15.33/15.51  thf('191', plain,
% 15.33/15.51      (![X0 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 15.33/15.51           = (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['137', '140', '141'])).
% 15.33/15.51  thf('192', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         ((k2_zfmisc_1 @ k1_xboole_0 @ X1) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['190', '191'])).
% 15.33/15.51  thf('193', plain,
% 15.33/15.51      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['189', '192'])).
% 15.33/15.51  thf('194', plain,
% 15.33/15.51      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 15.33/15.51      inference('demod', [status(thm)], ['114', '117', '124', '193'])).
% 15.33/15.51  thf('195', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.33/15.51         (((k1_xboole_0) != (k1_xboole_0))
% 15.33/15.51          | (r2_hidden @ X0 @ X1)
% 15.33/15.51          | (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ (k1_tarski @ X0)) @ 
% 15.33/15.51             (k2_zfmisc_1 @ X3 @ X1)))),
% 15.33/15.51      inference('demod', [status(thm)], ['13', '194'])).
% 15.33/15.51  thf('196', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.33/15.51         ((r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ (k1_tarski @ X0)) @ 
% 15.33/15.51           (k2_zfmisc_1 @ X3 @ X1))
% 15.33/15.51          | (r2_hidden @ X0 @ X1))),
% 15.33/15.51      inference('simplify', [status(thm)], ['195'])).
% 15.33/15.51  thf(t131_zfmisc_1, conjecture,
% 15.33/15.51    (![A:$i,B:$i,C:$i,D:$i]:
% 15.33/15.51     ( ( ( A ) != ( B ) ) =>
% 15.33/15.51       ( ( r1_xboole_0 @
% 15.33/15.51           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 15.33/15.51           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 15.33/15.51         ( r1_xboole_0 @
% 15.33/15.51           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 15.33/15.51           ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ))).
% 15.33/15.51  thf(zf_stmt_0, negated_conjecture,
% 15.33/15.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 15.33/15.51        ( ( ( A ) != ( B ) ) =>
% 15.33/15.51          ( ( r1_xboole_0 @
% 15.33/15.51              ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 15.33/15.51              ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 15.33/15.51            ( r1_xboole_0 @
% 15.33/15.51              ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 15.33/15.51              ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) )),
% 15.33/15.51    inference('cnf.neg', [status(esa)], [t131_zfmisc_1])).
% 15.33/15.51  thf('197', plain,
% 15.33/15.51      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 15.33/15.51           (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1))
% 15.33/15.51        | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 15.33/15.51             (k2_zfmisc_1 @ sk_D_1 @ (k1_tarski @ sk_B))))),
% 15.33/15.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.33/15.51  thf('198', plain,
% 15.33/15.51      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 15.33/15.51           (k2_zfmisc_1 @ sk_D_1 @ (k1_tarski @ sk_B))))
% 15.33/15.51         <= (~
% 15.33/15.51             ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 15.33/15.51               (k2_zfmisc_1 @ sk_D_1 @ (k1_tarski @ sk_B)))))),
% 15.33/15.51      inference('split', [status(esa)], ['197'])).
% 15.33/15.51  thf('199', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         (((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 15.33/15.51          | (r2_hidden @ X0 @ X1))),
% 15.33/15.51      inference('sup+', [status(thm)], ['5', '6'])).
% 15.33/15.51  thf('200', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.33/15.51         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 15.33/15.51            != (k1_xboole_0))
% 15.33/15.51          | (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1)))),
% 15.33/15.51      inference('sup-', [status(thm)], ['8', '11'])).
% 15.33/15.51  thf('201', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.33/15.51         (((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 15.33/15.51            != (k1_xboole_0))
% 15.33/15.51          | (r2_hidden @ X2 @ X3)
% 15.33/15.51          | (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X2) @ X0) @ 
% 15.33/15.51             (k2_zfmisc_1 @ X3 @ X1)))),
% 15.33/15.51      inference('sup-', [status(thm)], ['199', '200'])).
% 15.33/15.51  thf('202', plain,
% 15.33/15.51      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 15.33/15.51      inference('sup+', [status(thm)], ['189', '192'])).
% 15.33/15.51  thf('203', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.33/15.51         (((k1_xboole_0) != (k1_xboole_0))
% 15.33/15.51          | (r2_hidden @ X2 @ X3)
% 15.33/15.51          | (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X2) @ X0) @ 
% 15.33/15.51             (k2_zfmisc_1 @ X3 @ X1)))),
% 15.33/15.51      inference('demod', [status(thm)], ['201', '202'])).
% 15.33/15.51  thf('204', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.33/15.51         ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X2) @ X0) @ 
% 15.33/15.51           (k2_zfmisc_1 @ X3 @ X1))
% 15.33/15.51          | (r2_hidden @ X2 @ X3))),
% 15.33/15.51      inference('simplify', [status(thm)], ['203'])).
% 15.33/15.51  thf('205', plain,
% 15.33/15.51      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 15.33/15.51           (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1)))
% 15.33/15.51         <= (~
% 15.33/15.51             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 15.33/15.51               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1))))),
% 15.33/15.51      inference('split', [status(esa)], ['197'])).
% 15.33/15.51  thf('206', plain,
% 15.33/15.51      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 15.33/15.51         <= (~
% 15.33/15.51             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 15.33/15.51               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1))))),
% 15.33/15.51      inference('sup-', [status(thm)], ['204', '205'])).
% 15.33/15.51  thf('207', plain,
% 15.33/15.51      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 15.33/15.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 15.33/15.51  thf(d2_tarski, axiom,
% 15.33/15.51    (![A:$i,B:$i,C:$i]:
% 15.33/15.51     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 15.33/15.51       ( ![D:$i]:
% 15.33/15.51         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 15.33/15.51  thf('208', plain,
% 15.33/15.51      (![X18 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 15.33/15.51         (~ (r2_hidden @ X22 @ X20)
% 15.33/15.51          | ((X22) = (X21))
% 15.33/15.51          | ((X22) = (X18))
% 15.33/15.51          | ((X20) != (k2_tarski @ X21 @ X18)))),
% 15.33/15.51      inference('cnf', [status(esa)], [d2_tarski])).
% 15.33/15.51  thf('209', plain,
% 15.33/15.51      (![X18 : $i, X21 : $i, X22 : $i]:
% 15.33/15.51         (((X22) = (X18))
% 15.33/15.51          | ((X22) = (X21))
% 15.33/15.51          | ~ (r2_hidden @ X22 @ (k2_tarski @ X21 @ X18)))),
% 15.33/15.51      inference('simplify', [status(thm)], ['208'])).
% 15.33/15.51  thf('210', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 15.33/15.51      inference('sup-', [status(thm)], ['207', '209'])).
% 15.33/15.51  thf('211', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 15.33/15.51      inference('simplify', [status(thm)], ['210'])).
% 15.33/15.51  thf('212', plain,
% 15.33/15.51      ((((sk_A) = (sk_B)))
% 15.33/15.51         <= (~
% 15.33/15.51             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 15.33/15.51               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1))))),
% 15.33/15.51      inference('sup-', [status(thm)], ['206', '211'])).
% 15.33/15.51  thf('213', plain, (((sk_A) != (sk_B))),
% 15.33/15.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.33/15.51  thf('214', plain,
% 15.33/15.51      (((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 15.33/15.51         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1)))),
% 15.33/15.51      inference('simplify_reflect-', [status(thm)], ['212', '213'])).
% 15.33/15.51  thf('215', plain,
% 15.33/15.51      (~
% 15.33/15.51       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 15.33/15.51         (k2_zfmisc_1 @ sk_D_1 @ (k1_tarski @ sk_B)))) | 
% 15.33/15.51       ~
% 15.33/15.51       ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 15.33/15.51         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1)))),
% 15.33/15.51      inference('split', [status(esa)], ['197'])).
% 15.33/15.51  thf('216', plain,
% 15.33/15.51      (~
% 15.33/15.51       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 15.33/15.51         (k2_zfmisc_1 @ sk_D_1 @ (k1_tarski @ sk_B))))),
% 15.33/15.51      inference('sat_resolution*', [status(thm)], ['214', '215'])).
% 15.33/15.51  thf('217', plain,
% 15.33/15.51      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 15.33/15.51          (k2_zfmisc_1 @ sk_D_1 @ (k1_tarski @ sk_B)))),
% 15.33/15.51      inference('simpl_trail', [status(thm)], ['198', '216'])).
% 15.33/15.51  thf('218', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 15.33/15.51      inference('sup-', [status(thm)], ['196', '217'])).
% 15.33/15.51  thf('219', plain,
% 15.33/15.51      (![X0 : $i, X1 : $i]:
% 15.33/15.51         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 15.33/15.51      inference('simplify', [status(thm)], ['210'])).
% 15.33/15.51  thf('220', plain, (((sk_A) = (sk_B))),
% 15.33/15.51      inference('sup-', [status(thm)], ['218', '219'])).
% 15.33/15.51  thf('221', plain, (((sk_A) != (sk_B))),
% 15.33/15.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.33/15.51  thf('222', plain, ($false),
% 15.33/15.51      inference('simplify_reflect-', [status(thm)], ['220', '221'])).
% 15.33/15.51  
% 15.33/15.51  % SZS output end Refutation
% 15.33/15.51  
% 15.33/15.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
