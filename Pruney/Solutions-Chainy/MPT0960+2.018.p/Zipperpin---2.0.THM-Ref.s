%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jX2rz0RkxO

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:36 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 260 expanded)
%              Number of leaves         :   32 (  96 expanded)
%              Depth                    :   24
%              Number of atoms          : 1016 (2068 expanded)
%              Number of equality atoms :   56 ( 134 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

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
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ ( sk_C @ X13 @ X14 ) @ X14 )
      | ( r1_tarski @ ( k6_relat_1 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( X23
       != ( k1_wellord2 @ X22 ) )
      | ( ( k3_relat_1 @ X23 )
        = X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('9',plain,(
    ! [X22: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X22 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X22 ) )
        = X22 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('10',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('11',plain,(
    ! [X22: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i] :
      ( ( ( k3_relat_1 @ X5 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X5 ) @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ( ( k7_relat_1 @ X15 @ X16 )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( ( k7_relat_1 @ ( k1_wellord2 @ X0 ) @ X0 )
        = ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k1_wellord2 @ X0 ) @ X0 )
      = ( k1_wellord2 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_wellord1 @ X20 @ X19 )
        = ( k8_relat_1 @ X19 @ ( k7_relat_1 @ X20 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
        = ( k8_relat_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X22: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t30_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) )
        = A ) ) )).

thf('25',plain,(
    ! [X21: $i] :
      ( ( ( k2_wellord1 @ X21 @ ( k3_relat_1 @ X21 ) )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t30_wellord1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
        = ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
      = ( k1_wellord2 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_wellord2 @ X0 )
      = ( k8_relat_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','28','29'])).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) ) @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','36'])).

thf('38',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X23
       != ( k1_wellord2 @ X22 ) )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ~ ( r2_hidden @ X25 @ X22 )
      | ( r2_hidden @ ( k4_tarski @ X24 @ X25 ) @ X23 )
      | ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('43',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X22 ) )
      | ~ ( r1_tarski @ X24 @ X25 )
      | ( r2_hidden @ ( k4_tarski @ X24 @ X25 ) @ ( k1_wellord2 @ X22 ) )
      | ~ ( r2_hidden @ X25 @ X22 )
      | ~ ( r2_hidden @ X24 @ X22 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('45',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ( r2_hidden @ ( k4_tarski @ X24 @ X25 ) @ ( k1_wellord2 @ X22 ) )
      | ~ ( r2_hidden @ X25 @ X22 )
      | ~ ( r2_hidden @ X24 @ X22 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X13 @ X14 ) @ ( sk_C @ X13 @ X14 ) ) @ X13 )
      | ( r1_tarski @ ( k6_relat_1 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('56',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('57',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('60',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('61',plain,(
    ! [X8: $i] :
      ( ( r1_tarski @ X8 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X8 ) @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ ( sk_C @ X13 @ X14 ) @ X14 )
      | ( r1_tarski @ ( k6_relat_1 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('66',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('69',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X22: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('74',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k3_relat_1 @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X0 ) )
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X22: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('78',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','79'])).

thf('81',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X13 @ X14 ) @ ( sk_C @ X13 @ X14 ) ) @ X13 )
      | ( r1_tarski @ ( k6_relat_1 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('92',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('93',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('96',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['0','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jX2rz0RkxO
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 356 iterations in 0.160s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.43/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.43/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.43/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.43/0.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.43/0.61  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.43/0.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.43/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.43/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.61  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.43/0.61  thf(t33_wellord2, conjecture,
% 0.43/0.61    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t73_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ B ) =>
% 0.43/0.61       ( ( ![C:$i]:
% 0.43/0.61           ( ( r2_hidden @ C @ A ) => ( r2_hidden @ ( k4_tarski @ C @ C ) @ B ) ) ) =>
% 0.43/0.61         ( r1_tarski @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         ((r2_hidden @ (sk_C @ X13 @ X14) @ X14)
% 0.43/0.61          | (r1_tarski @ (k6_relat_1 @ X14) @ X13)
% 0.43/0.61          | ~ (v1_relat_1 @ X13))),
% 0.43/0.61      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.43/0.61  thf(t25_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( v1_relat_1 @ B ) =>
% 0.43/0.61           ( ( r1_tarski @ A @ B ) =>
% 0.43/0.61             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.43/0.61               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X9)
% 0.43/0.61          | (r1_tarski @ (k2_relat_1 @ X10) @ (k2_relat_1 @ X9))
% 0.43/0.61          | ~ (r1_tarski @ X10 @ X9)
% 0.43/0.61          | ~ (v1_relat_1 @ X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X0)
% 0.43/0.61          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.43/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.43/0.61          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X1)) @ (k2_relat_1 @ X0))
% 0.43/0.61          | ~ (v1_relat_1 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.43/0.61  thf(fc4_funct_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.43/0.61       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.43/0.61  thf('4', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.43/0.61  thf(t71_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.43/0.61       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.43/0.61  thf('5', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.43/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X0)
% 0.43/0.61          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.43/0.61          | (r1_tarski @ X1 @ (k2_relat_1 @ X0))
% 0.43/0.61          | ~ (v1_relat_1 @ X0))),
% 0.43/0.61      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((r1_tarski @ X1 @ (k2_relat_1 @ X0))
% 0.43/0.61          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.43/0.61          | ~ (v1_relat_1 @ X0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['6'])).
% 0.43/0.61  thf(d1_wellord2, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ B ) =>
% 0.43/0.61       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.43/0.61         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.43/0.61           ( ![C:$i,D:$i]:
% 0.43/0.61             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.43/0.61               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.43/0.61                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (![X22 : $i, X23 : $i]:
% 0.43/0.61         (((X23) != (k1_wellord2 @ X22))
% 0.43/0.61          | ((k3_relat_1 @ X23) = (X22))
% 0.43/0.61          | ~ (v1_relat_1 @ X23))),
% 0.43/0.61      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (![X22 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ (k1_wellord2 @ X22))
% 0.43/0.61          | ((k3_relat_1 @ (k1_wellord2 @ X22)) = (X22)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['8'])).
% 0.43/0.61  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.43/0.61  thf('10', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.43/0.61  thf('11', plain, (![X22 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X22)) = (X22))),
% 0.43/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.43/0.61  thf(d6_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( ( k3_relat_1 @ A ) =
% 0.43/0.61         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      (![X5 : $i]:
% 0.43/0.61         (((k3_relat_1 @ X5)
% 0.43/0.61            = (k2_xboole_0 @ (k1_relat_1 @ X5) @ (k2_relat_1 @ X5)))
% 0.43/0.61          | ~ (v1_relat_1 @ X5))),
% 0.43/0.61      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.43/0.61  thf(t7_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      (![X3 : $i, X4 : $i]: (r1_tarski @ X3 @ (k2_xboole_0 @ X3 @ X4))),
% 0.43/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.43/0.61          | ~ (v1_relat_1 @ X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['12', '13'])).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.43/0.61          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['11', '14'])).
% 0.43/0.61  thf('16', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.43/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.43/0.61  thf(t97_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ B ) =>
% 0.43/0.61       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.43/0.61         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (![X15 : $i, X16 : $i]:
% 0.43/0.61         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.43/0.61          | ((k7_relat_1 @ X15 @ X16) = (X15))
% 0.43/0.61          | ~ (v1_relat_1 @ X15))),
% 0.43/0.61      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.43/0.61          | ((k7_relat_1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.43/0.61  thf('20', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((k7_relat_1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))),
% 0.43/0.61      inference('demod', [status(thm)], ['19', '20'])).
% 0.43/0.61  thf(t18_wellord1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ B ) =>
% 0.43/0.61       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      (![X19 : $i, X20 : $i]:
% 0.43/0.61         (((k2_wellord1 @ X20 @ X19)
% 0.43/0.61            = (k8_relat_1 @ X19 @ (k7_relat_1 @ X20 @ X19)))
% 0.43/0.61          | ~ (v1_relat_1 @ X20))),
% 0.43/0.61      inference('cnf', [status(esa)], [t18_wellord1])).
% 0.43/0.61  thf('23', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k2_wellord1 @ (k1_wellord2 @ X0) @ X0)
% 0.43/0.61            = (k8_relat_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.43/0.61  thf('24', plain, (![X22 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X22)) = (X22))),
% 0.43/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.43/0.61  thf(t30_wellord1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ))).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      (![X21 : $i]:
% 0.43/0.61         (((k2_wellord1 @ X21 @ (k3_relat_1 @ X21)) = (X21))
% 0.43/0.61          | ~ (v1_relat_1 @ X21))),
% 0.43/0.61      inference('cnf', [status(esa)], [t30_wellord1])).
% 0.43/0.61  thf('26', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k2_wellord1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))
% 0.43/0.61          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['24', '25'])).
% 0.43/0.61  thf('27', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((k2_wellord1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))),
% 0.43/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.43/0.61  thf('29', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.43/0.61  thf('30', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((k1_wellord2 @ X0) = (k8_relat_1 @ X0 @ (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['23', '28', '29'])).
% 0.43/0.61  thf(t116_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ B ) =>
% 0.43/0.61       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i]:
% 0.43/0.61         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X6 @ X7)) @ X6)
% 0.43/0.61          | ~ (v1_relat_1 @ X7))),
% 0.43/0.61      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.43/0.61  thf('32', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.43/0.61          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['30', '31'])).
% 0.43/0.61  thf('33', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.43/0.61  thf('34', plain,
% 0.43/0.61      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.43/0.61      inference('demod', [status(thm)], ['32', '33'])).
% 0.43/0.61  thf(d10_xboole_0, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.61  thf('35', plain,
% 0.43/0.61      (![X0 : $i, X2 : $i]:
% 0.43/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.43/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.61  thf('36', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.43/0.61  thf('37', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.43/0.61          | (r2_hidden @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ X0)
% 0.43/0.61          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['7', '36'])).
% 0.43/0.61  thf('38', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.43/0.61  thf('39', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ X0)
% 0.43/0.61          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.43/0.61      inference('demod', [status(thm)], ['37', '38'])).
% 0.43/0.61  thf('40', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.43/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.61  thf('41', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.43/0.61      inference('simplify', [status(thm)], ['40'])).
% 0.43/0.61  thf('42', plain,
% 0.43/0.61      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.43/0.61         (((X23) != (k1_wellord2 @ X22))
% 0.43/0.61          | ~ (r2_hidden @ X24 @ X22)
% 0.43/0.61          | ~ (r2_hidden @ X25 @ X22)
% 0.43/0.61          | (r2_hidden @ (k4_tarski @ X24 @ X25) @ X23)
% 0.43/0.61          | ~ (r1_tarski @ X24 @ X25)
% 0.43/0.61          | ~ (v1_relat_1 @ X23))),
% 0.43/0.61      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.43/0.61  thf('43', plain,
% 0.43/0.61      (![X22 : $i, X24 : $i, X25 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ (k1_wellord2 @ X22))
% 0.43/0.61          | ~ (r1_tarski @ X24 @ X25)
% 0.43/0.61          | (r2_hidden @ (k4_tarski @ X24 @ X25) @ (k1_wellord2 @ X22))
% 0.43/0.61          | ~ (r2_hidden @ X25 @ X22)
% 0.43/0.61          | ~ (r2_hidden @ X24 @ X22))),
% 0.43/0.61      inference('simplify', [status(thm)], ['42'])).
% 0.43/0.61  thf('44', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.43/0.61  thf('45', plain,
% 0.43/0.61      (![X22 : $i, X24 : $i, X25 : $i]:
% 0.43/0.61         (~ (r1_tarski @ X24 @ X25)
% 0.43/0.61          | (r2_hidden @ (k4_tarski @ X24 @ X25) @ (k1_wellord2 @ X22))
% 0.43/0.61          | ~ (r2_hidden @ X25 @ X22)
% 0.43/0.61          | ~ (r2_hidden @ X24 @ X22))),
% 0.43/0.61      inference('demod', [status(thm)], ['43', '44'])).
% 0.43/0.61  thf('46', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.43/0.61          | ~ (r2_hidden @ X0 @ X1)
% 0.43/0.61          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['41', '45'])).
% 0.43/0.61  thf('47', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.43/0.61          | ~ (r2_hidden @ X0 @ X1))),
% 0.43/0.61      inference('simplify', [status(thm)], ['46'])).
% 0.43/0.61  thf('48', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | (r2_hidden @ 
% 0.43/0.61             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ 
% 0.43/0.61              (sk_C @ (k1_wellord2 @ X0) @ X0)) @ 
% 0.43/0.61             (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['39', '47'])).
% 0.43/0.61  thf('49', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         (~ (r2_hidden @ 
% 0.43/0.61             (k4_tarski @ (sk_C @ X13 @ X14) @ (sk_C @ X13 @ X14)) @ X13)
% 0.43/0.61          | (r1_tarski @ (k6_relat_1 @ X14) @ X13)
% 0.43/0.61          | ~ (v1_relat_1 @ X13))),
% 0.43/0.61      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.43/0.61  thf('50', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.43/0.61          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['48', '49'])).
% 0.43/0.61  thf('51', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.43/0.61  thf('52', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['50', '51'])).
% 0.43/0.61  thf('53', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X9)
% 0.43/0.61          | (r1_tarski @ (k2_relat_1 @ X10) @ (k2_relat_1 @ X9))
% 0.43/0.61          | ~ (r1_tarski @ X10 @ X9)
% 0.43/0.61          | ~ (v1_relat_1 @ X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.43/0.61  thf('54', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.43/0.61          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.43/0.61             (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['52', '53'])).
% 0.43/0.61  thf('55', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.43/0.61  thf('56', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.43/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.61  thf('57', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.43/0.61  thf('58', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | (r1_tarski @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.43/0.61      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.43/0.61  thf('59', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.43/0.61  thf('60', plain, (![X0 : $i]: ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('clc', [status(thm)], ['58', '59'])).
% 0.43/0.61  thf(t21_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( r1_tarski @
% 0.43/0.61         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.43/0.61  thf('61', plain,
% 0.43/0.61      (![X8 : $i]:
% 0.43/0.61         ((r1_tarski @ X8 @ 
% 0.43/0.61           (k2_zfmisc_1 @ (k1_relat_1 @ X8) @ (k2_relat_1 @ X8)))
% 0.43/0.61          | ~ (v1_relat_1 @ X8))),
% 0.43/0.61      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.43/0.61  thf('62', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.43/0.61           (k2_zfmisc_1 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0))
% 0.43/0.61          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['60', '61'])).
% 0.43/0.61  thf('63', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.43/0.61  thf('64', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.43/0.61          (k2_zfmisc_1 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0))),
% 0.43/0.61      inference('demod', [status(thm)], ['62', '63'])).
% 0.43/0.61  thf('65', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         ((r2_hidden @ (sk_C @ X13 @ X14) @ X14)
% 0.43/0.61          | (r1_tarski @ (k6_relat_1 @ X14) @ X13)
% 0.43/0.61          | ~ (v1_relat_1 @ X13))),
% 0.43/0.61      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.43/0.61  thf('66', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X9)
% 0.43/0.61          | (r1_tarski @ (k1_relat_1 @ X10) @ (k1_relat_1 @ X9))
% 0.43/0.61          | ~ (r1_tarski @ X10 @ X9)
% 0.43/0.61          | ~ (v1_relat_1 @ X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.43/0.61  thf('67', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X0)
% 0.43/0.61          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.43/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.43/0.61          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ (k1_relat_1 @ X0))
% 0.43/0.61          | ~ (v1_relat_1 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['65', '66'])).
% 0.43/0.61  thf('68', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.43/0.61  thf('69', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.43/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.61  thf('70', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X0)
% 0.43/0.61          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.43/0.61          | (r1_tarski @ X1 @ (k1_relat_1 @ X0))
% 0.43/0.61          | ~ (v1_relat_1 @ X0))),
% 0.43/0.61      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.43/0.61  thf('71', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((r1_tarski @ X1 @ (k1_relat_1 @ X0))
% 0.43/0.61          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.43/0.61          | ~ (v1_relat_1 @ X0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['70'])).
% 0.43/0.61  thf('72', plain, (![X22 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X22)) = (X22))),
% 0.43/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.43/0.61  thf('73', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.43/0.61          | ~ (v1_relat_1 @ X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['12', '13'])).
% 0.43/0.61  thf('74', plain,
% 0.43/0.61      (![X0 : $i, X2 : $i]:
% 0.43/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.43/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.61  thf('75', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X0)
% 0.43/0.61          | ~ (r1_tarski @ (k3_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.43/0.61          | ((k3_relat_1 @ X0) = (k1_relat_1 @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['73', '74'])).
% 0.43/0.61  thf('76', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | ((k3_relat_1 @ (k1_wellord2 @ X0))
% 0.43/0.61              = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['72', '75'])).
% 0.43/0.61  thf('77', plain, (![X22 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X22)) = (X22))),
% 0.43/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.43/0.61  thf('78', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.43/0.61  thf('79', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.43/0.61      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.43/0.61  thf('80', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.43/0.61          | (r2_hidden @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ X0)
% 0.43/0.61          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['71', '79'])).
% 0.43/0.61  thf('81', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.43/0.61  thf('82', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ X0)
% 0.43/0.61          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.43/0.61      inference('demod', [status(thm)], ['80', '81'])).
% 0.43/0.61  thf('83', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.43/0.61          | ~ (r2_hidden @ X0 @ X1))),
% 0.43/0.61      inference('simplify', [status(thm)], ['46'])).
% 0.43/0.61  thf('84', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | (r2_hidden @ 
% 0.43/0.61             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ 
% 0.43/0.61              (sk_C @ (k1_wellord2 @ X0) @ X0)) @ 
% 0.43/0.61             (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['82', '83'])).
% 0.43/0.61  thf('85', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         (~ (r2_hidden @ 
% 0.43/0.61             (k4_tarski @ (sk_C @ X13 @ X14) @ (sk_C @ X13 @ X14)) @ X13)
% 0.43/0.61          | (r1_tarski @ (k6_relat_1 @ X14) @ X13)
% 0.43/0.61          | ~ (v1_relat_1 @ X13))),
% 0.43/0.61      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.43/0.61  thf('86', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.43/0.61          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['84', '85'])).
% 0.43/0.61  thf('87', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.43/0.61  thf('88', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['86', '87'])).
% 0.43/0.61  thf('89', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X9)
% 0.43/0.61          | (r1_tarski @ (k1_relat_1 @ X10) @ (k1_relat_1 @ X9))
% 0.43/0.61          | ~ (r1_tarski @ X10 @ X9)
% 0.43/0.61          | ~ (v1_relat_1 @ X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.43/0.61  thf('90', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.43/0.61          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.43/0.61             (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['88', '89'])).
% 0.43/0.61  thf('91', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.43/0.61  thf('92', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.43/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.61  thf('93', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.43/0.61  thf('94', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.43/0.61      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.43/0.61  thf('95', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.43/0.61          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.43/0.61      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.43/0.61  thf('96', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.43/0.61      inference('clc', [status(thm)], ['94', '95'])).
% 0.43/0.61  thf('97', plain,
% 0.43/0.61      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.43/0.61      inference('demod', [status(thm)], ['64', '96'])).
% 0.43/0.61  thf('98', plain, ($false), inference('demod', [status(thm)], ['0', '97'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
