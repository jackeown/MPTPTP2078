%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LqC0kjWbbi

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:36 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 225 expanded)
%              Number of leaves         :   31 (  84 expanded)
%              Depth                    :   17
%              Number of atoms          :  738 (1706 expanded)
%              Number of equality atoms :   37 (  98 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25
       != ( k1_wellord2 @ X24 ) )
      | ( ( k3_relat_1 @ X25 )
        = X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X24: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X24 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X24 ) )
        = X24 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X24: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X24 ) )
      = X24 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t30_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X23: $i] :
      ( ( ( k2_wellord1 @ X23 @ ( k3_relat_1 @ X23 ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t30_wellord1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
        = ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
      = ( k1_wellord2 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_wellord1 @ X22 @ X21 )
        = ( k8_relat_1 @ X21 @ ( k7_relat_1 @ X22 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) ) @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( ( k8_relat_1 @ X9 @ X8 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( ( k8_relat_1 @ X0 @ ( k1_wellord2 @ X0 ) )
        = ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k1_wellord2 @ X0 ) )
      = ( k1_wellord2 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_wellord1 @ X20 @ X19 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X19 @ X20 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
        = ( k7_relat_1 @ ( k1_wellord2 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
      = ( k1_wellord2 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('24',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_wellord2 @ X0 )
      = ( k7_relat_1 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ ( k1_wellord2 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_wellord2 @ X0 )
      = ( k7_relat_1 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('31',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf(t73_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ! [C: $i] :
            ( ( r2_hidden @ C @ A )
           => ( r2_hidden @ ( k4_tarski @ C @ C ) @ B ) )
       => ( r1_tarski @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ ( sk_C @ X15 @ X16 ) @ X16 )
      | ( r1_tarski @ ( k6_relat_1 @ X16 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_wellord2 @ X24 ) )
      | ~ ( r2_hidden @ X26 @ X24 )
      | ~ ( r2_hidden @ X27 @ X24 )
      | ( r2_hidden @ ( k4_tarski @ X26 @ X27 ) @ X25 )
      | ~ ( r1_tarski @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('37',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X24 ) )
      | ~ ( r1_tarski @ X26 @ X27 )
      | ( r2_hidden @ ( k4_tarski @ X26 @ X27 ) @ ( k1_wellord2 @ X24 ) )
      | ~ ( r2_hidden @ X27 @ X24 )
      | ~ ( r2_hidden @ X26 @ X24 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('39',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ( r2_hidden @ ( k4_tarski @ X26 @ X27 ) @ ( k1_wellord2 @ X24 ) )
      | ~ ( r2_hidden @ X27 @ X24 )
      | ~ ( r2_hidden @ X26 @ X24 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X15 @ X16 ) @ ( sk_C @ X15 @ X16 ) ) @ X15 )
      | ( r1_tarski @ ( k6_relat_1 @ X16 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('46',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('51',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('52',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('53',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','54'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('56',plain,(
    ! [X10: $i] :
      ( ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('59',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('65',plain,(
    ! [X14: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('66',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','67'])).

thf('69',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LqC0kjWbbi
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:46:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.58/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.84  % Solved by: fo/fo7.sh
% 0.58/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.84  % done 582 iterations in 0.381s
% 0.58/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.84  % SZS output start Refutation
% 0.58/0.84  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.58/0.84  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.58/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.84  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.58/0.84  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.58/0.84  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.58/0.84  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.58/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.84  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.58/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.84  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.84  thf(t33_wellord2, conjecture,
% 0.58/0.84    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.58/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.84    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.58/0.84    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.58/0.84  thf('0', plain,
% 0.58/0.84      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf(d1_wellord2, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ B ) =>
% 0.58/0.84       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.58/0.84         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.58/0.84           ( ![C:$i,D:$i]:
% 0.58/0.84             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.58/0.84               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.58/0.84                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.58/0.84  thf('1', plain,
% 0.58/0.84      (![X24 : $i, X25 : $i]:
% 0.58/0.84         (((X25) != (k1_wellord2 @ X24))
% 0.58/0.84          | ((k3_relat_1 @ X25) = (X24))
% 0.58/0.84          | ~ (v1_relat_1 @ X25))),
% 0.58/0.84      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.58/0.84  thf('2', plain,
% 0.58/0.84      (![X24 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ (k1_wellord2 @ X24))
% 0.58/0.84          | ((k3_relat_1 @ (k1_wellord2 @ X24)) = (X24)))),
% 0.58/0.84      inference('simplify', [status(thm)], ['1'])).
% 0.58/0.84  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.58/0.84  thf('3', plain, (![X28 : $i]: (v1_relat_1 @ (k1_wellord2 @ X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.84  thf('4', plain, (![X24 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X24)) = (X24))),
% 0.58/0.84      inference('demod', [status(thm)], ['2', '3'])).
% 0.58/0.84  thf(t30_wellord1, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ A ) =>
% 0.58/0.84       ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ))).
% 0.58/0.84  thf('5', plain,
% 0.58/0.84      (![X23 : $i]:
% 0.58/0.84         (((k2_wellord1 @ X23 @ (k3_relat_1 @ X23)) = (X23))
% 0.58/0.84          | ~ (v1_relat_1 @ X23))),
% 0.58/0.84      inference('cnf', [status(esa)], [t30_wellord1])).
% 0.58/0.84  thf('6', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         (((k2_wellord1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))
% 0.58/0.84          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.58/0.84      inference('sup+', [status(thm)], ['4', '5'])).
% 0.58/0.84  thf('7', plain, (![X28 : $i]: (v1_relat_1 @ (k1_wellord2 @ X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.84  thf('8', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         ((k2_wellord1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))),
% 0.58/0.84      inference('demod', [status(thm)], ['6', '7'])).
% 0.58/0.84  thf(t18_wellord1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ B ) =>
% 0.58/0.84       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 0.58/0.84  thf('9', plain,
% 0.58/0.84      (![X21 : $i, X22 : $i]:
% 0.58/0.84         (((k2_wellord1 @ X22 @ X21)
% 0.58/0.84            = (k8_relat_1 @ X21 @ (k7_relat_1 @ X22 @ X21)))
% 0.58/0.84          | ~ (v1_relat_1 @ X22))),
% 0.58/0.84      inference('cnf', [status(esa)], [t18_wellord1])).
% 0.58/0.84  thf(t116_relat_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ B ) =>
% 0.58/0.84       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.58/0.84  thf('10', plain,
% 0.58/0.84      (![X6 : $i, X7 : $i]:
% 0.58/0.84         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X6 @ X7)) @ X6)
% 0.58/0.84          | ~ (v1_relat_1 @ X7))),
% 0.58/0.84      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.58/0.84  thf('11', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.58/0.84          | ~ (v1_relat_1 @ X1)
% 0.58/0.84          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.58/0.84      inference('sup+', [status(thm)], ['9', '10'])).
% 0.58/0.84  thf(dt_k7_relat_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.58/0.84  thf('12', plain,
% 0.58/0.84      (![X4 : $i, X5 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ X4) | (v1_relat_1 @ (k7_relat_1 @ X4 @ X5)))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.58/0.84  thf('13', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ X1)
% 0.58/0.84          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0))),
% 0.58/0.84      inference('clc', [status(thm)], ['11', '12'])).
% 0.58/0.84  thf('14', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         ((r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.58/0.84          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.58/0.84      inference('sup+', [status(thm)], ['8', '13'])).
% 0.58/0.84  thf('15', plain, (![X28 : $i]: (v1_relat_1 @ (k1_wellord2 @ X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.84  thf('16', plain,
% 0.58/0.84      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.58/0.84      inference('demod', [status(thm)], ['14', '15'])).
% 0.58/0.84  thf(t125_relat_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ B ) =>
% 0.58/0.84       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.58/0.84         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.58/0.84  thf('17', plain,
% 0.58/0.84      (![X8 : $i, X9 : $i]:
% 0.58/0.84         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.58/0.84          | ((k8_relat_1 @ X9 @ X8) = (X8))
% 0.58/0.84          | ~ (v1_relat_1 @ X8))),
% 0.58/0.84      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.58/0.84  thf('18', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.58/0.84          | ((k8_relat_1 @ X0 @ (k1_wellord2 @ X0)) = (k1_wellord2 @ X0)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.84  thf('19', plain, (![X28 : $i]: (v1_relat_1 @ (k1_wellord2 @ X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.84  thf('20', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         ((k8_relat_1 @ X0 @ (k1_wellord2 @ X0)) = (k1_wellord2 @ X0))),
% 0.58/0.84      inference('demod', [status(thm)], ['18', '19'])).
% 0.58/0.84  thf(t17_wellord1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ B ) =>
% 0.58/0.84       ( ( k2_wellord1 @ B @ A ) = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ))).
% 0.58/0.84  thf('21', plain,
% 0.58/0.84      (![X19 : $i, X20 : $i]:
% 0.58/0.84         (((k2_wellord1 @ X20 @ X19)
% 0.58/0.84            = (k7_relat_1 @ (k8_relat_1 @ X19 @ X20) @ X19))
% 0.58/0.84          | ~ (v1_relat_1 @ X20))),
% 0.58/0.84      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.58/0.84  thf('22', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         (((k2_wellord1 @ (k1_wellord2 @ X0) @ X0)
% 0.58/0.84            = (k7_relat_1 @ (k1_wellord2 @ X0) @ X0))
% 0.58/0.84          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.58/0.84      inference('sup+', [status(thm)], ['20', '21'])).
% 0.58/0.84  thf('23', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         ((k2_wellord1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))),
% 0.58/0.84      inference('demod', [status(thm)], ['6', '7'])).
% 0.58/0.84  thf('24', plain, (![X28 : $i]: (v1_relat_1 @ (k1_wellord2 @ X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.84  thf('25', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         ((k1_wellord2 @ X0) = (k7_relat_1 @ (k1_wellord2 @ X0) @ X0))),
% 0.58/0.84      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.58/0.84  thf(t87_relat_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ B ) =>
% 0.58/0.84       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.58/0.84  thf('26', plain,
% 0.58/0.84      (![X17 : $i, X18 : $i]:
% 0.58/0.84         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X17 @ X18)) @ X18)
% 0.58/0.84          | ~ (v1_relat_1 @ X17))),
% 0.58/0.84      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.58/0.84  thf(d10_xboole_0, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.84  thf('27', plain,
% 0.58/0.84      (![X0 : $i, X2 : $i]:
% 0.58/0.84         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.58/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.84  thf('28', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ X1)
% 0.58/0.84          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.58/0.84          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.58/0.84      inference('sup-', [status(thm)], ['26', '27'])).
% 0.58/0.84  thf('29', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.58/0.84          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ (k1_wellord2 @ X0) @ X0)))
% 0.58/0.84          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['25', '28'])).
% 0.58/0.84  thf('30', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         ((k1_wellord2 @ X0) = (k7_relat_1 @ (k1_wellord2 @ X0) @ X0))),
% 0.58/0.84      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.58/0.84  thf('31', plain, (![X28 : $i]: (v1_relat_1 @ (k1_wellord2 @ X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.84  thf('32', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.58/0.84          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.58/0.84      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.58/0.84  thf(t73_relat_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ B ) =>
% 0.58/0.84       ( ( ![C:$i]:
% 0.58/0.84           ( ( r2_hidden @ C @ A ) => ( r2_hidden @ ( k4_tarski @ C @ C ) @ B ) ) ) =>
% 0.58/0.84         ( r1_tarski @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.58/0.84  thf('33', plain,
% 0.58/0.84      (![X15 : $i, X16 : $i]:
% 0.58/0.84         ((r2_hidden @ (sk_C @ X15 @ X16) @ X16)
% 0.58/0.84          | (r1_tarski @ (k6_relat_1 @ X16) @ X15)
% 0.58/0.84          | ~ (v1_relat_1 @ X15))),
% 0.58/0.84      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.58/0.84  thf('34', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.58/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.84  thf('35', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.58/0.84      inference('simplify', [status(thm)], ['34'])).
% 0.58/0.84  thf('36', plain,
% 0.58/0.84      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.58/0.84         (((X25) != (k1_wellord2 @ X24))
% 0.58/0.84          | ~ (r2_hidden @ X26 @ X24)
% 0.58/0.84          | ~ (r2_hidden @ X27 @ X24)
% 0.58/0.84          | (r2_hidden @ (k4_tarski @ X26 @ X27) @ X25)
% 0.58/0.84          | ~ (r1_tarski @ X26 @ X27)
% 0.58/0.84          | ~ (v1_relat_1 @ X25))),
% 0.58/0.84      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.58/0.84  thf('37', plain,
% 0.58/0.84      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ (k1_wellord2 @ X24))
% 0.58/0.84          | ~ (r1_tarski @ X26 @ X27)
% 0.58/0.84          | (r2_hidden @ (k4_tarski @ X26 @ X27) @ (k1_wellord2 @ X24))
% 0.58/0.84          | ~ (r2_hidden @ X27 @ X24)
% 0.58/0.84          | ~ (r2_hidden @ X26 @ X24))),
% 0.58/0.84      inference('simplify', [status(thm)], ['36'])).
% 0.58/0.84  thf('38', plain, (![X28 : $i]: (v1_relat_1 @ (k1_wellord2 @ X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.84  thf('39', plain,
% 0.58/0.84      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.58/0.84         (~ (r1_tarski @ X26 @ X27)
% 0.58/0.84          | (r2_hidden @ (k4_tarski @ X26 @ X27) @ (k1_wellord2 @ X24))
% 0.58/0.84          | ~ (r2_hidden @ X27 @ X24)
% 0.58/0.84          | ~ (r2_hidden @ X26 @ X24))),
% 0.58/0.84      inference('demod', [status(thm)], ['37', '38'])).
% 0.58/0.84  thf('40', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (r2_hidden @ X0 @ X1)
% 0.58/0.84          | ~ (r2_hidden @ X0 @ X1)
% 0.58/0.84          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['35', '39'])).
% 0.58/0.84  thf('41', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.58/0.84          | ~ (r2_hidden @ X0 @ X1))),
% 0.58/0.84      inference('simplify', [status(thm)], ['40'])).
% 0.58/0.84  thf('42', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ X1)
% 0.58/0.84          | (r1_tarski @ (k6_relat_1 @ X0) @ X1)
% 0.58/0.84          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X1 @ X0)) @ 
% 0.58/0.84             (k1_wellord2 @ X0)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['33', '41'])).
% 0.58/0.84  thf('43', plain,
% 0.58/0.84      (![X15 : $i, X16 : $i]:
% 0.58/0.84         (~ (r2_hidden @ 
% 0.58/0.84             (k4_tarski @ (sk_C @ X15 @ X16) @ (sk_C @ X15 @ X16)) @ X15)
% 0.58/0.84          | (r1_tarski @ (k6_relat_1 @ X16) @ X15)
% 0.58/0.84          | ~ (v1_relat_1 @ X15))),
% 0.58/0.84      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.58/0.84  thf('44', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         ((r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0))
% 0.58/0.84          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.58/0.84          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.58/0.84          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.84  thf('45', plain, (![X28 : $i]: (v1_relat_1 @ (k1_wellord2 @ X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.84  thf('46', plain, (![X28 : $i]: (v1_relat_1 @ (k1_wellord2 @ X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.84  thf('47', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         ((r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0))
% 0.58/0.84          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.58/0.84      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.58/0.84  thf('48', plain,
% 0.58/0.84      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0))),
% 0.58/0.84      inference('simplify', [status(thm)], ['47'])).
% 0.58/0.84  thf(t25_relat_1, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ A ) =>
% 0.58/0.84       ( ![B:$i]:
% 0.58/0.84         ( ( v1_relat_1 @ B ) =>
% 0.58/0.84           ( ( r1_tarski @ A @ B ) =>
% 0.58/0.84             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.58/0.84               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.58/0.84  thf('49', plain,
% 0.58/0.84      (![X11 : $i, X12 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ X11)
% 0.58/0.84          | (r1_tarski @ (k1_relat_1 @ X12) @ (k1_relat_1 @ X11))
% 0.58/0.84          | ~ (r1_tarski @ X12 @ X11)
% 0.58/0.84          | ~ (v1_relat_1 @ X12))),
% 0.58/0.84      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.58/0.84  thf('50', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.58/0.84          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.58/0.84             (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.58/0.84          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.84  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.58/0.84  thf('51', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.84  thf(t71_relat_1, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.58/0.84       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.58/0.84  thf('52', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.58/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.84  thf('53', plain, (![X28 : $i]: (v1_relat_1 @ (k1_wellord2 @ X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.84  thf('54', plain,
% 0.58/0.84      (![X0 : $i]: (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.58/0.84      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.58/0.84  thf('55', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.58/0.84      inference('demod', [status(thm)], ['32', '54'])).
% 0.58/0.84  thf(t21_relat_1, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ A ) =>
% 0.58/0.84       ( r1_tarski @
% 0.58/0.84         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.58/0.84  thf('56', plain,
% 0.58/0.84      (![X10 : $i]:
% 0.58/0.84         ((r1_tarski @ X10 @ 
% 0.58/0.84           (k2_zfmisc_1 @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X10)))
% 0.58/0.84          | ~ (v1_relat_1 @ X10))),
% 0.58/0.84      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.58/0.84  thf('57', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         ((r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.58/0.84           (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))))
% 0.58/0.84          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.58/0.84      inference('sup+', [status(thm)], ['55', '56'])).
% 0.58/0.84  thf('58', plain,
% 0.58/0.84      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.58/0.84      inference('demod', [status(thm)], ['14', '15'])).
% 0.58/0.84  thf('59', plain,
% 0.58/0.84      (![X0 : $i, X2 : $i]:
% 0.58/0.84         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.58/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.84  thf('60', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.58/0.84          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.58/0.84      inference('sup-', [status(thm)], ['58', '59'])).
% 0.58/0.84  thf('61', plain,
% 0.58/0.84      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0))),
% 0.58/0.84      inference('simplify', [status(thm)], ['47'])).
% 0.58/0.84  thf('62', plain,
% 0.58/0.84      (![X11 : $i, X12 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ X11)
% 0.58/0.84          | (r1_tarski @ (k2_relat_1 @ X12) @ (k2_relat_1 @ X11))
% 0.58/0.84          | ~ (r1_tarski @ X12 @ X11)
% 0.58/0.84          | ~ (v1_relat_1 @ X12))),
% 0.58/0.84      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.58/0.84  thf('63', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.58/0.84          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.58/0.84             (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.58/0.84          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['61', '62'])).
% 0.58/0.84  thf('64', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.84  thf('65', plain, (![X14 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.58/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.84  thf('66', plain, (![X28 : $i]: (v1_relat_1 @ (k1_wellord2 @ X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.84  thf('67', plain,
% 0.58/0.84      (![X0 : $i]: (r1_tarski @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0)))),
% 0.58/0.84      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 0.58/0.84  thf('68', plain, (![X0 : $i]: ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))),
% 0.58/0.84      inference('demod', [status(thm)], ['60', '67'])).
% 0.58/0.84  thf('69', plain, (![X28 : $i]: (v1_relat_1 @ (k1_wellord2 @ X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.84  thf('70', plain,
% 0.58/0.84      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.58/0.84      inference('demod', [status(thm)], ['57', '68', '69'])).
% 0.58/0.84  thf('71', plain, ($false), inference('demod', [status(thm)], ['0', '70'])).
% 0.58/0.84  
% 0.58/0.84  % SZS output end Refutation
% 0.58/0.84  
% 0.71/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
