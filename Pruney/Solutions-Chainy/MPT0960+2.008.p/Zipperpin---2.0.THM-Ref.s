%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3YTpSBuIkP

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:34 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 162 expanded)
%              Number of leaves         :   25 (  61 expanded)
%              Depth                    :   18
%              Number of atoms          :  769 (1265 expanded)
%              Number of equality atoms :   34 (  65 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t33_wellord2,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t33_wellord2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_wellord2 @ sk_A ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t73_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ! [C: $i] :
            ( ( r2_hidden @ C @ A )
           => ( r2_hidden @ ( k4_tarski @ C @ C ) @ B ) )
       => ( r1_tarski @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_C @ X14 @ X15 ) @ X15 )
      | ( r1_tarski @ ( k6_relat_1 @ X15 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( r1_tarski @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17
       != ( k1_wellord2 @ X16 ) )
      | ( ( k3_relat_1 @ X17 )
        = X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('9',plain,(
    ! [X16: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X16 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X16 ) )
        = X16 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('10',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('11',plain,(
    ! [X16: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X7: $i] :
      ( ( ( k3_relat_1 @ X7 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','21'])).

thf('23',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17
       != ( k1_wellord2 @ X16 ) )
      | ~ ( r2_hidden @ X18 @ X16 )
      | ~ ( r2_hidden @ X19 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X17 )
      | ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('28',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X16 ) )
      | ~ ( r1_tarski @ X18 @ X19 )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ ( k1_wellord2 @ X16 ) )
      | ~ ( r2_hidden @ X19 @ X16 )
      | ~ ( r2_hidden @ X18 @ X16 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('30',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ ( k1_wellord2 @ X16 ) )
      | ~ ( r2_hidden @ X19 @ X16 )
      | ~ ( r2_hidden @ X18 @ X16 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X14 @ X15 ) @ ( sk_C @ X14 @ X15 ) ) @ X14 )
      | ( r1_tarski @ ( k6_relat_1 @ X15 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('41',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('42',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('46',plain,(
    ! [X9: $i] :
      ( ( r1_tarski @ X9 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X9 ) @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X16: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('51',plain,(
    ! [X7: $i] :
      ( ( ( k3_relat_1 @ X7 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_C @ X14 @ X15 ) @ X15 )
      | ( r1_tarski @ ( k6_relat_1 @ X15 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X14 @ X15 ) @ ( sk_C @ X14 @ X15 ) ) @ X14 )
      | ( r1_tarski @ ( k6_relat_1 @ X15 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('65',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('71',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('72',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['0','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3YTpSBuIkP
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:46:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.55/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.77  % Solved by: fo/fo7.sh
% 0.55/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.77  % done 355 iterations in 0.301s
% 0.55/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.77  % SZS output start Refutation
% 0.55/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.77  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.55/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.77  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.55/0.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.77  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.55/0.77  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.55/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.77  thf(t33_wellord2, conjecture,
% 0.55/0.77    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.55/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.77    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.55/0.77    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.55/0.77  thf('0', plain,
% 0.55/0.77      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf(t73_relat_1, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( v1_relat_1 @ B ) =>
% 0.55/0.77       ( ( ![C:$i]:
% 0.55/0.77           ( ( r2_hidden @ C @ A ) => ( r2_hidden @ ( k4_tarski @ C @ C ) @ B ) ) ) =>
% 0.55/0.77         ( r1_tarski @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.55/0.77  thf('1', plain,
% 0.55/0.77      (![X14 : $i, X15 : $i]:
% 0.55/0.77         ((r2_hidden @ (sk_C @ X14 @ X15) @ X15)
% 0.55/0.77          | (r1_tarski @ (k6_relat_1 @ X15) @ X14)
% 0.55/0.77          | ~ (v1_relat_1 @ X14))),
% 0.55/0.77      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.55/0.77  thf(t25_relat_1, axiom,
% 0.55/0.77    (![A:$i]:
% 0.55/0.77     ( ( v1_relat_1 @ A ) =>
% 0.55/0.77       ( ![B:$i]:
% 0.55/0.77         ( ( v1_relat_1 @ B ) =>
% 0.55/0.77           ( ( r1_tarski @ A @ B ) =>
% 0.55/0.77             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.55/0.77               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.55/0.77  thf('2', plain,
% 0.55/0.77      (![X10 : $i, X11 : $i]:
% 0.55/0.77         (~ (v1_relat_1 @ X10)
% 0.55/0.77          | (r1_tarski @ (k2_relat_1 @ X11) @ (k2_relat_1 @ X10))
% 0.55/0.77          | ~ (r1_tarski @ X11 @ X10)
% 0.55/0.77          | ~ (v1_relat_1 @ X11))),
% 0.55/0.77      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.55/0.77  thf('3', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         (~ (v1_relat_1 @ X0)
% 0.55/0.77          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.55/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.55/0.77          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X1)) @ (k2_relat_1 @ X0))
% 0.55/0.77          | ~ (v1_relat_1 @ X0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.77  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.55/0.77  thf('4', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.55/0.77  thf(t71_relat_1, axiom,
% 0.55/0.77    (![A:$i]:
% 0.55/0.77     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.55/0.77       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.55/0.77  thf('5', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.55/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.55/0.77  thf('6', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         (~ (v1_relat_1 @ X0)
% 0.55/0.77          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.55/0.77          | (r1_tarski @ X1 @ (k2_relat_1 @ X0))
% 0.55/0.77          | ~ (v1_relat_1 @ X0))),
% 0.55/0.77      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.55/0.77  thf('7', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         ((r1_tarski @ X1 @ (k2_relat_1 @ X0))
% 0.55/0.77          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.55/0.77          | ~ (v1_relat_1 @ X0))),
% 0.55/0.77      inference('simplify', [status(thm)], ['6'])).
% 0.55/0.77  thf(d1_wellord2, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( v1_relat_1 @ B ) =>
% 0.55/0.77       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.55/0.77         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.55/0.77           ( ![C:$i,D:$i]:
% 0.55/0.77             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.55/0.77               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.55/0.77                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.55/0.77  thf('8', plain,
% 0.55/0.77      (![X16 : $i, X17 : $i]:
% 0.55/0.77         (((X17) != (k1_wellord2 @ X16))
% 0.55/0.77          | ((k3_relat_1 @ X17) = (X16))
% 0.55/0.77          | ~ (v1_relat_1 @ X17))),
% 0.55/0.77      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.55/0.77  thf('9', plain,
% 0.55/0.77      (![X16 : $i]:
% 0.55/0.77         (~ (v1_relat_1 @ (k1_wellord2 @ X16))
% 0.55/0.77          | ((k3_relat_1 @ (k1_wellord2 @ X16)) = (X16)))),
% 0.55/0.77      inference('simplify', [status(thm)], ['8'])).
% 0.55/0.77  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.55/0.77  thf('10', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.55/0.77  thf('11', plain, (![X16 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X16)) = (X16))),
% 0.55/0.77      inference('demod', [status(thm)], ['9', '10'])).
% 0.55/0.77  thf(d6_relat_1, axiom,
% 0.55/0.77    (![A:$i]:
% 0.55/0.77     ( ( v1_relat_1 @ A ) =>
% 0.55/0.77       ( ( k3_relat_1 @ A ) =
% 0.55/0.77         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.55/0.77  thf('12', plain,
% 0.55/0.77      (![X7 : $i]:
% 0.55/0.77         (((k3_relat_1 @ X7)
% 0.55/0.77            = (k2_xboole_0 @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X7)))
% 0.55/0.77          | ~ (v1_relat_1 @ X7))),
% 0.55/0.77      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.55/0.77  thf(commutativity_k2_xboole_0, axiom,
% 0.55/0.77    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.55/0.77  thf('13', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.77      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.55/0.77  thf(t7_xboole_1, axiom,
% 0.55/0.77    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.55/0.77  thf('14', plain,
% 0.55/0.77      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.55/0.77      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.55/0.77  thf('15', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.55/0.77      inference('sup+', [status(thm)], ['13', '14'])).
% 0.55/0.77  thf('16', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.55/0.77          | ~ (v1_relat_1 @ X0))),
% 0.55/0.77      inference('sup+', [status(thm)], ['12', '15'])).
% 0.55/0.77  thf('17', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.55/0.77          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.55/0.77      inference('sup+', [status(thm)], ['11', '16'])).
% 0.55/0.77  thf('18', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.55/0.77  thf('19', plain,
% 0.55/0.77      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.55/0.77      inference('demod', [status(thm)], ['17', '18'])).
% 0.55/0.77  thf(d10_xboole_0, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.77  thf('20', plain,
% 0.55/0.77      (![X2 : $i, X4 : $i]:
% 0.55/0.77         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.55/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.77  thf('21', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.55/0.77          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['19', '20'])).
% 0.55/0.77  thf('22', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.55/0.77          | (r2_hidden @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ X0)
% 0.55/0.77          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['7', '21'])).
% 0.55/0.77  thf('23', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.55/0.77  thf('24', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ X0)
% 0.55/0.77          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.55/0.77      inference('demod', [status(thm)], ['22', '23'])).
% 0.55/0.77  thf('25', plain,
% 0.55/0.77      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.55/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.77  thf('26', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.55/0.77      inference('simplify', [status(thm)], ['25'])).
% 0.55/0.77  thf('27', plain,
% 0.55/0.77      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.55/0.77         (((X17) != (k1_wellord2 @ X16))
% 0.55/0.77          | ~ (r2_hidden @ X18 @ X16)
% 0.55/0.77          | ~ (r2_hidden @ X19 @ X16)
% 0.55/0.77          | (r2_hidden @ (k4_tarski @ X18 @ X19) @ X17)
% 0.55/0.77          | ~ (r1_tarski @ X18 @ X19)
% 0.55/0.77          | ~ (v1_relat_1 @ X17))),
% 0.55/0.77      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.55/0.77  thf('28', plain,
% 0.55/0.77      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.55/0.77         (~ (v1_relat_1 @ (k1_wellord2 @ X16))
% 0.55/0.77          | ~ (r1_tarski @ X18 @ X19)
% 0.55/0.77          | (r2_hidden @ (k4_tarski @ X18 @ X19) @ (k1_wellord2 @ X16))
% 0.55/0.77          | ~ (r2_hidden @ X19 @ X16)
% 0.55/0.77          | ~ (r2_hidden @ X18 @ X16))),
% 0.55/0.77      inference('simplify', [status(thm)], ['27'])).
% 0.55/0.77  thf('29', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.55/0.77  thf('30', plain,
% 0.55/0.77      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.55/0.77         (~ (r1_tarski @ X18 @ X19)
% 0.55/0.77          | (r2_hidden @ (k4_tarski @ X18 @ X19) @ (k1_wellord2 @ X16))
% 0.55/0.77          | ~ (r2_hidden @ X19 @ X16)
% 0.55/0.77          | ~ (r2_hidden @ X18 @ X16))),
% 0.55/0.77      inference('demod', [status(thm)], ['28', '29'])).
% 0.55/0.77  thf('31', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         (~ (r2_hidden @ X0 @ X1)
% 0.55/0.77          | ~ (r2_hidden @ X0 @ X1)
% 0.55/0.77          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['26', '30'])).
% 0.55/0.77  thf('32', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.55/0.77          | ~ (r2_hidden @ X0 @ X1))),
% 0.55/0.77      inference('simplify', [status(thm)], ['31'])).
% 0.55/0.77  thf('33', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.55/0.77          | (r2_hidden @ 
% 0.55/0.77             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ 
% 0.55/0.77              (sk_C @ (k1_wellord2 @ X0) @ X0)) @ 
% 0.55/0.77             (k1_wellord2 @ X0)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['24', '32'])).
% 0.55/0.77  thf('34', plain,
% 0.55/0.77      (![X14 : $i, X15 : $i]:
% 0.55/0.77         (~ (r2_hidden @ 
% 0.55/0.77             (k4_tarski @ (sk_C @ X14 @ X15) @ (sk_C @ X14 @ X15)) @ X14)
% 0.55/0.77          | (r1_tarski @ (k6_relat_1 @ X15) @ X14)
% 0.55/0.77          | ~ (v1_relat_1 @ X14))),
% 0.55/0.77      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.55/0.77  thf('35', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.55/0.77          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.55/0.77          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['33', '34'])).
% 0.55/0.77  thf('36', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.55/0.77  thf('37', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.55/0.77          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.55/0.77      inference('demod', [status(thm)], ['35', '36'])).
% 0.55/0.77  thf('38', plain,
% 0.55/0.77      (![X10 : $i, X11 : $i]:
% 0.55/0.77         (~ (v1_relat_1 @ X10)
% 0.55/0.77          | (r1_tarski @ (k2_relat_1 @ X11) @ (k2_relat_1 @ X10))
% 0.55/0.77          | ~ (r1_tarski @ X11 @ X10)
% 0.55/0.77          | ~ (v1_relat_1 @ X11))),
% 0.55/0.77      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.55/0.77  thf('39', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.55/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.55/0.77          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.55/0.77             (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.55/0.77          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['37', '38'])).
% 0.55/0.77  thf('40', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.55/0.77  thf('41', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.55/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.55/0.77  thf('42', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.55/0.77  thf('43', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.55/0.77          | (r1_tarski @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.55/0.77      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.55/0.77  thf('44', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.55/0.77          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['19', '20'])).
% 0.55/0.77  thf('45', plain, (![X0 : $i]: ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))),
% 0.55/0.77      inference('clc', [status(thm)], ['43', '44'])).
% 0.55/0.77  thf(t21_relat_1, axiom,
% 0.55/0.77    (![A:$i]:
% 0.55/0.77     ( ( v1_relat_1 @ A ) =>
% 0.55/0.77       ( r1_tarski @
% 0.55/0.77         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.55/0.77  thf('46', plain,
% 0.55/0.77      (![X9 : $i]:
% 0.55/0.77         ((r1_tarski @ X9 @ 
% 0.55/0.77           (k2_zfmisc_1 @ (k1_relat_1 @ X9) @ (k2_relat_1 @ X9)))
% 0.55/0.77          | ~ (v1_relat_1 @ X9))),
% 0.55/0.77      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.55/0.77  thf('47', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.55/0.77           (k2_zfmisc_1 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0))
% 0.55/0.77          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.55/0.77      inference('sup+', [status(thm)], ['45', '46'])).
% 0.55/0.77  thf('48', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.55/0.77  thf('49', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.55/0.77          (k2_zfmisc_1 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0))),
% 0.55/0.77      inference('demod', [status(thm)], ['47', '48'])).
% 0.55/0.77  thf('50', plain, (![X16 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X16)) = (X16))),
% 0.55/0.77      inference('demod', [status(thm)], ['9', '10'])).
% 0.55/0.77  thf('51', plain,
% 0.55/0.77      (![X7 : $i]:
% 0.55/0.77         (((k3_relat_1 @ X7)
% 0.55/0.77            = (k2_xboole_0 @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X7)))
% 0.55/0.77          | ~ (v1_relat_1 @ X7))),
% 0.55/0.77      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.55/0.77  thf('52', plain,
% 0.55/0.77      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.55/0.77      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.55/0.77  thf('53', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.55/0.77          | ~ (v1_relat_1 @ X0))),
% 0.55/0.77      inference('sup+', [status(thm)], ['51', '52'])).
% 0.55/0.77  thf('54', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.55/0.77          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.55/0.77      inference('sup+', [status(thm)], ['50', '53'])).
% 0.55/0.77  thf('55', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.55/0.77  thf('56', plain,
% 0.55/0.77      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.55/0.77      inference('demod', [status(thm)], ['54', '55'])).
% 0.55/0.77  thf('57', plain,
% 0.55/0.77      (![X2 : $i, X4 : $i]:
% 0.55/0.77         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.55/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.77  thf('58', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.55/0.77          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['56', '57'])).
% 0.55/0.77  thf('59', plain,
% 0.55/0.77      (![X14 : $i, X15 : $i]:
% 0.55/0.77         ((r2_hidden @ (sk_C @ X14 @ X15) @ X15)
% 0.55/0.77          | (r1_tarski @ (k6_relat_1 @ X15) @ X14)
% 0.55/0.77          | ~ (v1_relat_1 @ X14))),
% 0.55/0.77      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.55/0.77  thf('60', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.55/0.77          | ~ (r2_hidden @ X0 @ X1))),
% 0.55/0.77      inference('simplify', [status(thm)], ['31'])).
% 0.55/0.77  thf('61', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i]:
% 0.55/0.77         (~ (v1_relat_1 @ X1)
% 0.55/0.77          | (r1_tarski @ (k6_relat_1 @ X0) @ X1)
% 0.55/0.77          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X1 @ X0)) @ 
% 0.55/0.77             (k1_wellord2 @ X0)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['59', '60'])).
% 0.55/0.77  thf('62', plain,
% 0.55/0.77      (![X14 : $i, X15 : $i]:
% 0.55/0.77         (~ (r2_hidden @ 
% 0.55/0.77             (k4_tarski @ (sk_C @ X14 @ X15) @ (sk_C @ X14 @ X15)) @ X14)
% 0.55/0.77          | (r1_tarski @ (k6_relat_1 @ X15) @ X14)
% 0.55/0.77          | ~ (v1_relat_1 @ X14))),
% 0.55/0.77      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.55/0.77  thf('63', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0))
% 0.55/0.77          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.55/0.77          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.55/0.77          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['61', '62'])).
% 0.55/0.77  thf('64', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.55/0.77  thf('65', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.55/0.77  thf('66', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0))
% 0.55/0.77          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.55/0.77      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.55/0.77  thf('67', plain,
% 0.55/0.77      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0))),
% 0.55/0.77      inference('simplify', [status(thm)], ['66'])).
% 0.55/0.77  thf('68', plain,
% 0.55/0.77      (![X10 : $i, X11 : $i]:
% 0.55/0.77         (~ (v1_relat_1 @ X10)
% 0.55/0.77          | (r1_tarski @ (k1_relat_1 @ X11) @ (k1_relat_1 @ X10))
% 0.55/0.77          | ~ (r1_tarski @ X11 @ X10)
% 0.55/0.77          | ~ (v1_relat_1 @ X11))),
% 0.55/0.77      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.55/0.77  thf('69', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.55/0.77          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.55/0.77             (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.55/0.77          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['67', '68'])).
% 0.55/0.77  thf('70', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.55/0.77  thf('71', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.55/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.55/0.77  thf('72', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.55/0.77  thf('73', plain,
% 0.55/0.77      (![X0 : $i]: (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.55/0.77      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.55/0.77  thf('74', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.55/0.77      inference('demod', [status(thm)], ['58', '73'])).
% 0.55/0.77  thf('75', plain,
% 0.55/0.77      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.55/0.77      inference('demod', [status(thm)], ['49', '74'])).
% 0.55/0.77  thf('76', plain, ($false), inference('demod', [status(thm)], ['0', '75'])).
% 0.55/0.77  
% 0.55/0.77  % SZS output end Refutation
% 0.55/0.77  
% 0.55/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
