%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tzI4HkIP2S

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:35 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 302 expanded)
%              Number of leaves         :   34 ( 110 expanded)
%              Depth                    :   23
%              Number of atoms          : 1051 (2388 expanded)
%              Number of equality atoms :   53 ( 138 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ ( sk_C @ X17 @ X18 ) @ X18 )
      | ( r1_tarski @ ( k6_relat_1 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( X27
       != ( k1_wellord2 @ X26 ) )
      | ( ( k3_relat_1 @ X27 )
        = X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('9',plain,(
    ! [X26: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X26 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X26 ) )
        = X26 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('10',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('11',plain,(
    ! [X26: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X26 ) )
      = X26 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t30_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) )
        = A ) ) )).

thf('12',plain,(
    ! [X25: $i] :
      ( ( ( k2_wellord1 @ X25 @ ( k3_relat_1 @ X25 ) )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t30_wellord1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
        = ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
      = ( k1_wellord2 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_wellord1 @ X24 @ X23 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X23 @ X24 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X19 @ X20 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_wellord1 @ X1 @ X0 ) @ ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_wellord1 @ X1 @ X0 ) @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k8_relat_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k8_relat_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X10 @ X11 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_wellord2 @ X0 )
        = ( k8_relat_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_wellord2 @ X0 )
      = ( k8_relat_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X8 @ X9 ) ) @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_wellord2 @ X0 )
      = ( k8_relat_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('35',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','36'])).

thf('38',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X30 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X27
       != ( k1_wellord2 @ X26 ) )
      | ~ ( r2_hidden @ X28 @ X26 )
      | ~ ( r2_hidden @ X29 @ X26 )
      | ( r2_hidden @ ( k4_tarski @ X28 @ X29 ) @ X27 )
      | ~ ( r1_tarski @ X28 @ X29 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('43',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( r1_tarski @ X28 @ X29 )
      | ( r2_hidden @ ( k4_tarski @ X28 @ X29 ) @ ( k1_wellord2 @ X26 ) )
      | ~ ( r2_hidden @ X29 @ X26 )
      | ~ ( r2_hidden @ X28 @ X26 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('45',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X28 @ X29 )
      | ( r2_hidden @ ( k4_tarski @ X28 @ X29 ) @ ( k1_wellord2 @ X26 ) )
      | ~ ( r2_hidden @ X29 @ X26 )
      | ~ ( r2_hidden @ X28 @ X26 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X17 @ X18 ) @ ( sk_C @ X17 @ X18 ) ) @ X17 )
      | ( r1_tarski @ ( k6_relat_1 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('56',plain,(
    ! [X16: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('57',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X30 ) ) ),
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
    inference(demod,[status(thm)],['33','34','35'])).

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
    ! [X12: $i] :
      ( ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ ( sk_C @ X17 @ X18 ) @ X18 )
      | ( r1_tarski @ ( k6_relat_1 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('66',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('69',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
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
    ! [X26: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X26 ) )
      = X26 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('73',plain,(
    ! [X5: $i] :
      ( ( ( k3_relat_1 @ X5 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X5 ) @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('74',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','80'])).

thf('82',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X17 @ X18 ) @ ( sk_C @ X17 @ X18 ) ) @ X17 )
      | ( r1_tarski @ ( k6_relat_1 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('93',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('94',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('97',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['0','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tzI4HkIP2S
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 11:38:00 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 303 iterations in 0.124s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.60  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.38/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.60  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.38/0.60  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.38/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.60  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.38/0.60  thf(t33_wellord2, conjecture,
% 0.38/0.60    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.38/0.60  thf('0', plain,
% 0.38/0.60      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(t73_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ B ) =>
% 0.38/0.60       ( ( ![C:$i]:
% 0.38/0.60           ( ( r2_hidden @ C @ A ) => ( r2_hidden @ ( k4_tarski @ C @ C ) @ B ) ) ) =>
% 0.38/0.60         ( r1_tarski @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.38/0.60  thf('1', plain,
% 0.38/0.60      (![X17 : $i, X18 : $i]:
% 0.38/0.60         ((r2_hidden @ (sk_C @ X17 @ X18) @ X18)
% 0.38/0.60          | (r1_tarski @ (k6_relat_1 @ X18) @ X17)
% 0.38/0.60          | ~ (v1_relat_1 @ X17))),
% 0.38/0.60      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.38/0.60  thf(t25_relat_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ A ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( v1_relat_1 @ B ) =>
% 0.38/0.60           ( ( r1_tarski @ A @ B ) =>
% 0.38/0.60             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.38/0.60               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      (![X13 : $i, X14 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X13)
% 0.38/0.60          | (r1_tarski @ (k2_relat_1 @ X14) @ (k2_relat_1 @ X13))
% 0.38/0.60          | ~ (r1_tarski @ X14 @ X13)
% 0.38/0.60          | ~ (v1_relat_1 @ X14))),
% 0.38/0.60      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X0)
% 0.38/0.60          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.38/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.38/0.60          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X1)) @ (k2_relat_1 @ X0))
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.60  thf(fc3_funct_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.38/0.60       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.38/0.60  thf('4', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.60  thf(t71_relat_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.38/0.60       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.60  thf('5', plain, (![X16 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.38/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.60  thf('6', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X0)
% 0.38/0.60          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.38/0.60          | (r1_tarski @ X1 @ (k2_relat_1 @ X0))
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.38/0.60  thf('7', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((r1_tarski @ X1 @ (k2_relat_1 @ X0))
% 0.38/0.60          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.60  thf(d1_wellord2, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ B ) =>
% 0.38/0.60       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.38/0.60         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.38/0.60           ( ![C:$i,D:$i]:
% 0.38/0.60             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.38/0.60               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.38/0.60                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      (![X26 : $i, X27 : $i]:
% 0.38/0.60         (((X27) != (k1_wellord2 @ X26))
% 0.38/0.60          | ((k3_relat_1 @ X27) = (X26))
% 0.38/0.60          | ~ (v1_relat_1 @ X27))),
% 0.38/0.60      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.38/0.60  thf('9', plain,
% 0.38/0.60      (![X26 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ (k1_wellord2 @ X26))
% 0.38/0.60          | ((k3_relat_1 @ (k1_wellord2 @ X26)) = (X26)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['8'])).
% 0.38/0.60  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.38/0.60  thf('10', plain, (![X30 : $i]: (v1_relat_1 @ (k1_wellord2 @ X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.60  thf('11', plain, (![X26 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X26)) = (X26))),
% 0.38/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.60  thf(t30_wellord1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ A ) =>
% 0.38/0.60       ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      (![X25 : $i]:
% 0.38/0.60         (((k2_wellord1 @ X25 @ (k3_relat_1 @ X25)) = (X25))
% 0.38/0.60          | ~ (v1_relat_1 @ X25))),
% 0.38/0.60      inference('cnf', [status(esa)], [t30_wellord1])).
% 0.38/0.60  thf('13', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((k2_wellord1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))
% 0.38/0.60          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.60  thf('14', plain, (![X30 : $i]: (v1_relat_1 @ (k1_wellord2 @ X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((k2_wellord1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))),
% 0.38/0.60      inference('demod', [status(thm)], ['13', '14'])).
% 0.38/0.60  thf(t17_wellord1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ B ) =>
% 0.38/0.60       ( ( k2_wellord1 @ B @ A ) = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ))).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      (![X23 : $i, X24 : $i]:
% 0.38/0.60         (((k2_wellord1 @ X24 @ X23)
% 0.38/0.60            = (k7_relat_1 @ (k8_relat_1 @ X23 @ X24) @ X23))
% 0.38/0.60          | ~ (v1_relat_1 @ X24))),
% 0.38/0.60      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.38/0.60  thf(t88_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.38/0.60  thf('17', plain,
% 0.38/0.60      (![X19 : $i, X20 : $i]:
% 0.38/0.60         ((r1_tarski @ (k7_relat_1 @ X19 @ X20) @ X19) | ~ (v1_relat_1 @ X19))),
% 0.38/0.60      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.38/0.60  thf('18', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((r1_tarski @ (k2_wellord1 @ X1 @ X0) @ (k8_relat_1 @ X0 @ X1))
% 0.38/0.60          | ~ (v1_relat_1 @ X1)
% 0.38/0.60          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['16', '17'])).
% 0.38/0.60  thf(dt_k8_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.38/0.60  thf('19', plain,
% 0.38/0.60      (![X6 : $i, X7 : $i]:
% 0.38/0.60         ((v1_relat_1 @ (k8_relat_1 @ X6 @ X7)) | ~ (v1_relat_1 @ X7))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.38/0.60  thf('20', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X1)
% 0.38/0.60          | (r1_tarski @ (k2_wellord1 @ X1 @ X0) @ (k8_relat_1 @ X0 @ X1)))),
% 0.38/0.60      inference('clc', [status(thm)], ['18', '19'])).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.38/0.60           (k8_relat_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['15', '20'])).
% 0.38/0.60  thf('22', plain, (![X30 : $i]: (v1_relat_1 @ (k1_wellord2 @ X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.38/0.60          (k8_relat_1 @ X0 @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.60  thf(t117_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      (![X10 : $i, X11 : $i]:
% 0.38/0.60         ((r1_tarski @ (k8_relat_1 @ X10 @ X11) @ X11) | ~ (v1_relat_1 @ X11))),
% 0.38/0.60      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.38/0.60  thf(d10_xboole_0, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      (![X0 : $i, X2 : $i]:
% 0.38/0.60         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.60  thf('26', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X0)
% 0.38/0.60          | ~ (r1_tarski @ X0 @ (k8_relat_1 @ X1 @ X0))
% 0.38/0.60          | ((X0) = (k8_relat_1 @ X1 @ X0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.60  thf('27', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((k1_wellord2 @ X0) = (k8_relat_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['23', '26'])).
% 0.38/0.60  thf('28', plain, (![X30 : $i]: (v1_relat_1 @ (k1_wellord2 @ X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((k1_wellord2 @ X0) = (k8_relat_1 @ X0 @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.60  thf(t116_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ B ) =>
% 0.38/0.60       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.38/0.60  thf('30', plain,
% 0.38/0.60      (![X8 : $i, X9 : $i]:
% 0.38/0.60         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X8 @ X9)) @ X8)
% 0.38/0.60          | ~ (v1_relat_1 @ X9))),
% 0.38/0.60      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.38/0.60  thf('31', plain,
% 0.38/0.60      (![X0 : $i, X2 : $i]:
% 0.38/0.60         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.60  thf('32', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X1)
% 0.38/0.60          | ~ (r1_tarski @ X0 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)))
% 0.38/0.60          | ((X0) = (k2_relat_1 @ (k8_relat_1 @ X0 @ X1))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.60  thf('33', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | ((X0) = (k2_relat_1 @ (k8_relat_1 @ X0 @ (k1_wellord2 @ X0))))
% 0.38/0.60          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['29', '32'])).
% 0.38/0.60  thf('34', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((k1_wellord2 @ X0) = (k8_relat_1 @ X0 @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.60  thf('35', plain, (![X30 : $i]: (v1_relat_1 @ (k1_wellord2 @ X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.60  thf('36', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.38/0.60  thf('37', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.38/0.60          | (r2_hidden @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ X0)
% 0.38/0.60          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['7', '36'])).
% 0.38/0.60  thf('38', plain, (![X30 : $i]: (v1_relat_1 @ (k1_wellord2 @ X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.60  thf('39', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ X0)
% 0.38/0.60          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['37', '38'])).
% 0.38/0.60  thf('40', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.60  thf('41', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.60      inference('simplify', [status(thm)], ['40'])).
% 0.38/0.60  thf('42', plain,
% 0.38/0.60      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.60         (((X27) != (k1_wellord2 @ X26))
% 0.38/0.60          | ~ (r2_hidden @ X28 @ X26)
% 0.38/0.60          | ~ (r2_hidden @ X29 @ X26)
% 0.38/0.60          | (r2_hidden @ (k4_tarski @ X28 @ X29) @ X27)
% 0.38/0.60          | ~ (r1_tarski @ X28 @ X29)
% 0.38/0.60          | ~ (v1_relat_1 @ X27))),
% 0.38/0.60      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.38/0.60  thf('43', plain,
% 0.38/0.60      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ (k1_wellord2 @ X26))
% 0.38/0.60          | ~ (r1_tarski @ X28 @ X29)
% 0.38/0.60          | (r2_hidden @ (k4_tarski @ X28 @ X29) @ (k1_wellord2 @ X26))
% 0.38/0.60          | ~ (r2_hidden @ X29 @ X26)
% 0.38/0.60          | ~ (r2_hidden @ X28 @ X26))),
% 0.38/0.60      inference('simplify', [status(thm)], ['42'])).
% 0.38/0.60  thf('44', plain, (![X30 : $i]: (v1_relat_1 @ (k1_wellord2 @ X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.60  thf('45', plain,
% 0.38/0.60      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.38/0.60         (~ (r1_tarski @ X28 @ X29)
% 0.38/0.60          | (r2_hidden @ (k4_tarski @ X28 @ X29) @ (k1_wellord2 @ X26))
% 0.38/0.60          | ~ (r2_hidden @ X29 @ X26)
% 0.38/0.60          | ~ (r2_hidden @ X28 @ X26))),
% 0.38/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.38/0.60  thf('46', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.60          | ~ (r2_hidden @ X0 @ X1)
% 0.38/0.60          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['41', '45'])).
% 0.38/0.60  thf('47', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.38/0.60          | ~ (r2_hidden @ X0 @ X1))),
% 0.38/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.38/0.60  thf('48', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | (r2_hidden @ 
% 0.38/0.60             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ 
% 0.38/0.60              (sk_C @ (k1_wellord2 @ X0) @ X0)) @ 
% 0.38/0.60             (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['39', '47'])).
% 0.38/0.60  thf('49', plain,
% 0.38/0.60      (![X17 : $i, X18 : $i]:
% 0.38/0.60         (~ (r2_hidden @ 
% 0.38/0.60             (k4_tarski @ (sk_C @ X17 @ X18) @ (sk_C @ X17 @ X18)) @ X17)
% 0.38/0.60          | (r1_tarski @ (k6_relat_1 @ X18) @ X17)
% 0.38/0.60          | ~ (v1_relat_1 @ X17))),
% 0.38/0.60      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.38/0.60  thf('50', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.38/0.60          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.60  thf('51', plain, (![X30 : $i]: (v1_relat_1 @ (k1_wellord2 @ X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.60  thf('52', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('demod', [status(thm)], ['50', '51'])).
% 0.38/0.60  thf('53', plain,
% 0.38/0.60      (![X13 : $i, X14 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X13)
% 0.38/0.60          | (r1_tarski @ (k2_relat_1 @ X14) @ (k2_relat_1 @ X13))
% 0.38/0.60          | ~ (r1_tarski @ X14 @ X13)
% 0.38/0.60          | ~ (v1_relat_1 @ X14))),
% 0.38/0.60      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.38/0.60  thf('54', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.38/0.60          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.38/0.60             (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.60  thf('55', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.60  thf('56', plain, (![X16 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.38/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.60  thf('57', plain, (![X30 : $i]: (v1_relat_1 @ (k1_wellord2 @ X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.60  thf('58', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | (r1_tarski @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.38/0.60  thf('59', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.38/0.60  thf('60', plain, (![X0 : $i]: ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('clc', [status(thm)], ['58', '59'])).
% 0.38/0.60  thf(t21_relat_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ A ) =>
% 0.38/0.60       ( r1_tarski @
% 0.38/0.60         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.38/0.60  thf('61', plain,
% 0.38/0.60      (![X12 : $i]:
% 0.38/0.60         ((r1_tarski @ X12 @ 
% 0.38/0.60           (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.38/0.60          | ~ (v1_relat_1 @ X12))),
% 0.38/0.60      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.38/0.60  thf('62', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.38/0.60           (k2_zfmisc_1 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0))
% 0.38/0.60          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['60', '61'])).
% 0.38/0.60  thf('63', plain, (![X30 : $i]: (v1_relat_1 @ (k1_wellord2 @ X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.60  thf('64', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.38/0.60          (k2_zfmisc_1 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0))),
% 0.38/0.60      inference('demod', [status(thm)], ['62', '63'])).
% 0.38/0.60  thf('65', plain,
% 0.38/0.60      (![X17 : $i, X18 : $i]:
% 0.38/0.60         ((r2_hidden @ (sk_C @ X17 @ X18) @ X18)
% 0.38/0.60          | (r1_tarski @ (k6_relat_1 @ X18) @ X17)
% 0.38/0.60          | ~ (v1_relat_1 @ X17))),
% 0.38/0.60      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.38/0.60  thf('66', plain,
% 0.38/0.60      (![X13 : $i, X14 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X13)
% 0.38/0.60          | (r1_tarski @ (k1_relat_1 @ X14) @ (k1_relat_1 @ X13))
% 0.38/0.60          | ~ (r1_tarski @ X14 @ X13)
% 0.38/0.60          | ~ (v1_relat_1 @ X14))),
% 0.38/0.60      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.38/0.60  thf('67', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X0)
% 0.38/0.60          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.38/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.38/0.60          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ (k1_relat_1 @ X0))
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['65', '66'])).
% 0.38/0.60  thf('68', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.60  thf('69', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.38/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.60  thf('70', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X0)
% 0.38/0.60          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.38/0.60          | (r1_tarski @ X1 @ (k1_relat_1 @ X0))
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.38/0.60  thf('71', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((r1_tarski @ X1 @ (k1_relat_1 @ X0))
% 0.38/0.60          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['70'])).
% 0.38/0.60  thf('72', plain, (![X26 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X26)) = (X26))),
% 0.38/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.60  thf(d6_relat_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ A ) =>
% 0.38/0.60       ( ( k3_relat_1 @ A ) =
% 0.38/0.60         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.38/0.60  thf('73', plain,
% 0.38/0.60      (![X5 : $i]:
% 0.38/0.60         (((k3_relat_1 @ X5)
% 0.38/0.60            = (k2_xboole_0 @ (k1_relat_1 @ X5) @ (k2_relat_1 @ X5)))
% 0.38/0.60          | ~ (v1_relat_1 @ X5))),
% 0.38/0.60      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.38/0.60  thf(t7_xboole_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.60  thf('74', plain,
% 0.38/0.60      (![X3 : $i, X4 : $i]: (r1_tarski @ X3 @ (k2_xboole_0 @ X3 @ X4))),
% 0.38/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.38/0.60  thf('75', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('sup+', [status(thm)], ['73', '74'])).
% 0.38/0.60  thf('76', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['72', '75'])).
% 0.38/0.60  thf('77', plain, (![X30 : $i]: (v1_relat_1 @ (k1_wellord2 @ X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.60  thf('78', plain,
% 0.38/0.60      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.38/0.60      inference('demod', [status(thm)], ['76', '77'])).
% 0.38/0.60  thf('79', plain,
% 0.38/0.60      (![X0 : $i, X2 : $i]:
% 0.38/0.60         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.60  thf('80', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['78', '79'])).
% 0.38/0.60  thf('81', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.38/0.60          | (r2_hidden @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ X0)
% 0.38/0.60          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['71', '80'])).
% 0.38/0.60  thf('82', plain, (![X30 : $i]: (v1_relat_1 @ (k1_wellord2 @ X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.60  thf('83', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ X0)
% 0.38/0.60          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['81', '82'])).
% 0.38/0.60  thf('84', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.38/0.60          | ~ (r2_hidden @ X0 @ X1))),
% 0.38/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.38/0.60  thf('85', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | (r2_hidden @ 
% 0.38/0.60             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ 
% 0.38/0.60              (sk_C @ (k1_wellord2 @ X0) @ X0)) @ 
% 0.38/0.60             (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['83', '84'])).
% 0.38/0.60  thf('86', plain,
% 0.38/0.60      (![X17 : $i, X18 : $i]:
% 0.38/0.60         (~ (r2_hidden @ 
% 0.38/0.60             (k4_tarski @ (sk_C @ X17 @ X18) @ (sk_C @ X17 @ X18)) @ X17)
% 0.38/0.60          | (r1_tarski @ (k6_relat_1 @ X18) @ X17)
% 0.38/0.60          | ~ (v1_relat_1 @ X17))),
% 0.38/0.60      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.38/0.60  thf('87', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.38/0.60          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['85', '86'])).
% 0.38/0.60  thf('88', plain, (![X30 : $i]: (v1_relat_1 @ (k1_wellord2 @ X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.60  thf('89', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('demod', [status(thm)], ['87', '88'])).
% 0.38/0.60  thf('90', plain,
% 0.38/0.60      (![X13 : $i, X14 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X13)
% 0.38/0.60          | (r1_tarski @ (k1_relat_1 @ X14) @ (k1_relat_1 @ X13))
% 0.38/0.60          | ~ (r1_tarski @ X14 @ X13)
% 0.38/0.60          | ~ (v1_relat_1 @ X14))),
% 0.38/0.60      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.38/0.60  thf('91', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.38/0.60          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.38/0.60             (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['89', '90'])).
% 0.38/0.60  thf('92', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.60  thf('93', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.38/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.60  thf('94', plain, (![X30 : $i]: (v1_relat_1 @ (k1_wellord2 @ X30))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.60  thf('95', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.38/0.60  thf('96', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.60          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['78', '79'])).
% 0.38/0.60  thf('97', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.60      inference('clc', [status(thm)], ['95', '96'])).
% 0.38/0.60  thf('98', plain,
% 0.38/0.60      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.38/0.60      inference('demod', [status(thm)], ['64', '97'])).
% 0.38/0.60  thf('99', plain, ($false), inference('demod', [status(thm)], ['0', '98'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
