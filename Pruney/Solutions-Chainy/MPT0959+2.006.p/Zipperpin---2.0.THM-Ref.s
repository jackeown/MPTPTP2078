%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y9cQ971lyo

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:33 EST 2020

% Result     : Theorem 7.23s
% Output     : Refutation 7.27s
% Verified   : 
% Statistics : Number of formulae       :  204 (18032 expanded)
%              Number of leaves         :   27 (5471 expanded)
%              Depth                    :   49
%              Number of atoms          : 1915 (191716 expanded)
%              Number of equality atoms :  194 (17020 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t32_wellord2,conjecture,(
    ! [A: $i] :
      ( ( k1_wellord2 @ ( k1_tarski @ A ) )
      = ( k1_tarski @ ( k4_tarski @ A @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_wellord2 @ ( k1_tarski @ A ) )
        = ( k1_tarski @ ( k4_tarski @ A @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_wellord2])).

thf('0',plain,(
    ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ ( k2_tarski @ X20 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

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

thf('9',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33
       != ( k1_wellord2 @ X32 ) )
      | ( ( k3_relat_1 @ X33 )
        = X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('10',plain,(
    ! [X32: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X32 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X32 ) )
        = X32 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('11',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('12',plain,(
    ! [X32: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X32 ) )
      = X32 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X24 @ X25 ) @ ( sk_D @ X24 @ X25 ) ) @ X25 )
      | ( r1_tarski @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X30 ) @ X31 )
      | ( r2_hidden @ X29 @ ( k3_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( X7 = X4 )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('21',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( ( sk_C_2 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X32: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X32 ) )
      = X32 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X24 @ X25 ) @ ( sk_D @ X24 @ X25 ) ) @ X25 )
      | ( r1_tarski @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('25',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X30 ) @ X31 )
      | ( r2_hidden @ X30 @ ( k3_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( ( sk_D @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X24 @ X25 ) @ ( sk_D @ X24 @ X25 ) ) @ X24 )
      | ( r1_tarski @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','39'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X12 @ X12 @ X13 @ X14 )
      = ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_enumset1 @ X10 @ X10 @ X11 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X12 @ X12 @ X13 @ X14 )
      = ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('47',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X18
        = ( k1_enumset1 @ X15 @ X16 @ X17 ) )
      | ( X18
        = ( k2_tarski @ X15 @ X17 ) )
      | ( X18
        = ( k2_tarski @ X16 @ X17 ) )
      | ( X18
        = ( k2_tarski @ X15 @ X16 ) )
      | ( X18
        = ( k1_tarski @ X17 ) )
      | ( X18
        = ( k1_tarski @ X16 ) )
      | ( X18
        = ( k1_tarski @ X15 ) )
      | ( X18 = k1_xboole_0 )
      | ~ ( r1_tarski @ X18 @ ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X3
        = ( k1_tarski @ X2 ) )
      | ( X3
        = ( k1_tarski @ X1 ) )
      | ( X3
        = ( k1_tarski @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X1 ) )
      | ( X3
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X0 ) )
      | ( X3
        = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_enumset1 @ X10 @ X10 @ X11 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('51',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('52',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('53',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('54',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k1_wellord2 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) )
      | ( ( k1_wellord2 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','56'])).

thf('58',plain,(
    ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
     != ( k1_wellord2 @ ( k1_tarski @ sk_A ) ) )
    | ( ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','60'])).

thf('62',plain,
    ( ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['59'])).

thf('63',plain,(
    ! [X32: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X32 ) )
      = X32 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('64',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('66',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ ( k2_tarski @ X20 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ k1_xboole_0 ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','39'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X1 )
      | ( ( sk_D @ X1 @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) )
        = ( k4_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X1 )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X1 )
      | ( ( sk_C_2 @ X1 @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) )
        = ( k4_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X24 @ X25 ) @ ( sk_D @ X24 @ X25 ) ) @ X24 )
      | ( r1_tarski @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( k4_tarski @ X0 @ X0 ) @ ( sk_D @ X1 @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ) ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( k4_tarski @ X0 @ X0 ) @ ( sk_D @ X1 @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ) ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( k4_tarski @ X0 @ X0 ) @ ( sk_D @ X1 @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( k4_tarski @ X0 @ X0 ) @ ( k4_tarski @ X0 @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( k4_tarski @ X0 @ X0 ) @ ( k4_tarski @ X0 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ ( k1_tarski @ ( k4_tarski @ ( k4_tarski @ X0 @ X0 ) @ ( k4_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = ( k1_tarski @ ( k4_tarski @ ( k4_tarski @ X0 @ X0 ) @ ( k4_tarski @ X0 @ X0 ) ) ) )
      | ( ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k1_wellord2 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) )
      | ( ( k1_wellord2 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','56'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k1_wellord2 @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) )
        = ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = k1_xboole_0 )
      | ( ( k1_wellord2 @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X32: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X32 ) )
      = X32 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) )
        = ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) )
      | ( ( k1_wellord2 @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) )
        = k1_xboole_0 )
      | ( ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X32: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X32 ) )
      = X32 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k1_wellord2 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) )
      | ( ( k1_wellord2 @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) )
        = k1_xboole_0 )
      | ( ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X32: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X32 ) )
      = X32 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) )
      | ( ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = k1_xboole_0 )
      | ( ( k1_wellord2 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','60'])).

thf('101',plain,
    ( ( k1_xboole_0
     != ( k1_wellord2 @ ( k1_tarski @ sk_A ) ) )
    | ( ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ sk_A ) ) )
      = k1_xboole_0 )
    | ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('103',plain,
    ( ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['59'])).

thf('104',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('105',plain,
    ( ( k1_wellord2 @ ( k3_relat_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('107',plain,
    ( ( k1_wellord2 @ ( k3_relat_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['103','104'])).

thf('108',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_wellord2 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['101','102','105','106','107'])).

thf('109',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_A ) ) )
    | ( ( k1_wellord2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('111',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ ( k3_relat_1 @ k1_xboole_0 ) )
    | ( ( k1_wellord2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('113',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ k1_xboole_0 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( k1_wellord2 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k4_tarski @ sk_A @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,
    ( ( ( k1_wellord2 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k4_tarski @ sk_A @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('117',plain,
    ( ( ( k1_wellord2 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k4_tarski @ sk_A @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = ( k1_tarski @ ( k4_tarski @ ( k4_tarski @ X0 @ X0 ) @ ( k4_tarski @ X0 @ X0 ) ) ) )
      | ( ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('119',plain,
    ( ( ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ sk_A ) ) )
      = ( k1_tarski @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_A ) @ sk_A ) ) )
    | ( ( k1_wellord2 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_wellord2 @ ( k1_wellord2 @ ( k1_tarski @ sk_A ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('121',plain,
    ( ( k1_wellord2 @ ( k3_relat_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['103','104'])).

thf('122',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('123',plain,
    ( ( k1_wellord2 @ ( k3_relat_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['103','104'])).

thf('124',plain,
    ( ( ( k1_wellord2 @ k1_xboole_0 )
      = ( k1_tarski @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_A ) @ sk_A ) ) )
    | ( ( k1_wellord2 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_wellord2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['119','120','121','122','123'])).

thf('125',plain,
    ( ( ( k1_wellord2 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_wellord2 @ k1_xboole_0 )
      = ( k1_tarski @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_A ) @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ( ( k1_wellord2 @ k1_xboole_0 )
      = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_A ) ) )
    | ( ( k1_wellord2 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_wellord2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['116','125'])).

thf('127',plain,
    ( ( ( k1_wellord2 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_wellord2 @ k1_xboole_0 )
      = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( ( k1_wellord2 @ k1_xboole_0 )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_wellord2 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_wellord2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['115','127'])).

thf('129',plain,
    ( ( ( k1_wellord2 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_wellord2 @ k1_xboole_0 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_wellord2 @ k1_xboole_0 ) @ X0 )
      | ( ( k1_wellord2 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('133',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('134',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('135',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_enumset1 @ X10 @ X10 @ X11 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('136',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ( r1_tarski @ X19 @ ( k1_enumset1 @ X15 @ X16 @ X17 ) )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('137',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['135','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['134','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['133','141'])).

thf('143',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( ( sk_C @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
       != ( sk_C @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( ( sk_C @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('148',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ k1_xboole_0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_wellord2 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['132','150'])).

thf('152',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ k1_xboole_0 ) @ X1 )
      | ( ( sk_D @ X1 @ ( k1_wellord2 @ k1_xboole_0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
       != ( sk_D @ X0 @ ( k1_wellord2 @ k1_xboole_0 ) ) )
      | ( r1_tarski @ ( k1_wellord2 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ k1_xboole_0 ) @ X1 )
      | ( ( sk_D @ X1 @ ( k1_wellord2 @ k1_xboole_0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('157',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ k1_xboole_0 ) @ X0 ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k1_wellord2 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['131','157'])).

thf('159',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k1_wellord2 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k1_wellord2 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( ( k1_wellord2 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_wellord2 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_wellord2 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( k1_wellord2 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['163'])).

thf('165',plain,(
    ! [X32: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X32 ) )
      = X32 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('166',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('168',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['68','166','167'])).

thf('169',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('170',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('172',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['164','165'])).

thf('173',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['61','170','173'])).

thf('175',plain,(
    $false ),
    inference(simplify,[status(thm)],['174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y9cQ971lyo
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:24:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 7.23/7.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.23/7.44  % Solved by: fo/fo7.sh
% 7.23/7.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.23/7.44  % done 5304 iterations in 6.966s
% 7.23/7.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.23/7.44  % SZS output start Refutation
% 7.23/7.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.23/7.44  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 7.23/7.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 7.23/7.44  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 7.23/7.44  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.23/7.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.23/7.44  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 7.23/7.44  thf(sk_A_type, type, sk_A: $i).
% 7.23/7.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.23/7.44  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 7.23/7.44  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 7.23/7.44  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 7.23/7.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.23/7.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 7.23/7.44  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 7.23/7.44  thf(t32_wellord2, conjecture,
% 7.23/7.44    (![A:$i]:
% 7.23/7.44     ( ( k1_wellord2 @ ( k1_tarski @ A ) ) =
% 7.23/7.44       ( k1_tarski @ ( k4_tarski @ A @ A ) ) ))).
% 7.23/7.44  thf(zf_stmt_0, negated_conjecture,
% 7.23/7.44    (~( ![A:$i]:
% 7.23/7.44        ( ( k1_wellord2 @ ( k1_tarski @ A ) ) =
% 7.23/7.44          ( k1_tarski @ ( k4_tarski @ A @ A ) ) ) )),
% 7.23/7.44    inference('cnf.neg', [status(esa)], [t32_wellord2])).
% 7.23/7.44  thf('0', plain,
% 7.23/7.44      (((k1_wellord2 @ (k1_tarski @ sk_A))
% 7.23/7.44         != (k1_tarski @ (k4_tarski @ sk_A @ sk_A)))),
% 7.23/7.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.23/7.44  thf(t69_enumset1, axiom,
% 7.23/7.44    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 7.23/7.44  thf('1', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 7.23/7.44      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.23/7.44  thf(d3_tarski, axiom,
% 7.23/7.44    (![A:$i,B:$i]:
% 7.23/7.44     ( ( r1_tarski @ A @ B ) <=>
% 7.23/7.44       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 7.23/7.44  thf('2', plain,
% 7.23/7.44      (![X1 : $i, X3 : $i]:
% 7.23/7.44         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.23/7.44      inference('cnf', [status(esa)], [d3_tarski])).
% 7.23/7.44  thf('3', plain,
% 7.23/7.44      (![X1 : $i, X3 : $i]:
% 7.23/7.44         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 7.23/7.44      inference('cnf', [status(esa)], [d3_tarski])).
% 7.23/7.44  thf('4', plain,
% 7.23/7.44      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 7.23/7.44      inference('sup-', [status(thm)], ['2', '3'])).
% 7.23/7.44  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 7.23/7.44      inference('simplify', [status(thm)], ['4'])).
% 7.23/7.44  thf(t38_zfmisc_1, axiom,
% 7.23/7.44    (![A:$i,B:$i,C:$i]:
% 7.23/7.44     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 7.23/7.44       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 7.23/7.44  thf('6', plain,
% 7.23/7.44      (![X20 : $i, X21 : $i, X22 : $i]:
% 7.23/7.44         ((r2_hidden @ X20 @ X21)
% 7.23/7.44          | ~ (r1_tarski @ (k2_tarski @ X20 @ X22) @ X21))),
% 7.23/7.44      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 7.23/7.44  thf('7', plain,
% 7.23/7.44      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 7.23/7.44      inference('sup-', [status(thm)], ['5', '6'])).
% 7.23/7.44  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 7.23/7.44      inference('sup+', [status(thm)], ['1', '7'])).
% 7.27/7.44  thf(d1_wellord2, axiom,
% 7.27/7.44    (![A:$i,B:$i]:
% 7.27/7.44     ( ( v1_relat_1 @ B ) =>
% 7.27/7.44       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 7.27/7.44         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 7.27/7.44           ( ![C:$i,D:$i]:
% 7.27/7.44             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 7.27/7.44               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 7.27/7.44                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 7.27/7.44  thf('9', plain,
% 7.27/7.44      (![X32 : $i, X33 : $i]:
% 7.27/7.44         (((X33) != (k1_wellord2 @ X32))
% 7.27/7.44          | ((k3_relat_1 @ X33) = (X32))
% 7.27/7.44          | ~ (v1_relat_1 @ X33))),
% 7.27/7.44      inference('cnf', [status(esa)], [d1_wellord2])).
% 7.27/7.44  thf('10', plain,
% 7.27/7.44      (![X32 : $i]:
% 7.27/7.44         (~ (v1_relat_1 @ (k1_wellord2 @ X32))
% 7.27/7.44          | ((k3_relat_1 @ (k1_wellord2 @ X32)) = (X32)))),
% 7.27/7.44      inference('simplify', [status(thm)], ['9'])).
% 7.27/7.44  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 7.27/7.44  thf('11', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 7.27/7.44      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 7.27/7.44  thf('12', plain, (![X32 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X32)) = (X32))),
% 7.27/7.44      inference('demod', [status(thm)], ['10', '11'])).
% 7.27/7.44  thf(d3_relat_1, axiom,
% 7.27/7.44    (![A:$i]:
% 7.27/7.44     ( ( v1_relat_1 @ A ) =>
% 7.27/7.44       ( ![B:$i]:
% 7.27/7.44         ( ( r1_tarski @ A @ B ) <=>
% 7.27/7.44           ( ![C:$i,D:$i]:
% 7.27/7.44             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 7.27/7.44               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 7.27/7.44  thf('13', plain,
% 7.27/7.44      (![X24 : $i, X25 : $i]:
% 7.27/7.44         ((r2_hidden @ 
% 7.27/7.44           (k4_tarski @ (sk_C_2 @ X24 @ X25) @ (sk_D @ X24 @ X25)) @ X25)
% 7.27/7.44          | (r1_tarski @ X25 @ X24)
% 7.27/7.44          | ~ (v1_relat_1 @ X25))),
% 7.27/7.44      inference('cnf', [status(esa)], [d3_relat_1])).
% 7.27/7.44  thf(t30_relat_1, axiom,
% 7.27/7.44    (![A:$i,B:$i,C:$i]:
% 7.27/7.44     ( ( v1_relat_1 @ C ) =>
% 7.27/7.44       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 7.27/7.44         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 7.27/7.44           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 7.27/7.44  thf('14', plain,
% 7.27/7.44      (![X29 : $i, X30 : $i, X31 : $i]:
% 7.27/7.44         (~ (r2_hidden @ (k4_tarski @ X29 @ X30) @ X31)
% 7.27/7.44          | (r2_hidden @ X29 @ (k3_relat_1 @ X31))
% 7.27/7.44          | ~ (v1_relat_1 @ X31))),
% 7.27/7.44      inference('cnf', [status(esa)], [t30_relat_1])).
% 7.27/7.44  thf('15', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         (~ (v1_relat_1 @ X0)
% 7.27/7.44          | (r1_tarski @ X0 @ X1)
% 7.27/7.44          | ~ (v1_relat_1 @ X0)
% 7.27/7.44          | (r2_hidden @ (sk_C_2 @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['13', '14'])).
% 7.27/7.44  thf('16', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r2_hidden @ (sk_C_2 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 7.27/7.44          | (r1_tarski @ X0 @ X1)
% 7.27/7.44          | ~ (v1_relat_1 @ X0))),
% 7.27/7.44      inference('simplify', [status(thm)], ['15'])).
% 7.27/7.44  thf('17', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r2_hidden @ (sk_C_2 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 7.27/7.44          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 7.27/7.44      inference('sup+', [status(thm)], ['12', '16'])).
% 7.27/7.44  thf('18', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 7.27/7.44      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 7.27/7.44  thf('19', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r2_hidden @ (sk_C_2 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 7.27/7.44      inference('demod', [status(thm)], ['17', '18'])).
% 7.27/7.44  thf(d1_tarski, axiom,
% 7.27/7.44    (![A:$i,B:$i]:
% 7.27/7.44     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 7.27/7.44       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 7.27/7.44  thf('20', plain,
% 7.27/7.44      (![X4 : $i, X6 : $i, X7 : $i]:
% 7.27/7.44         (~ (r2_hidden @ X7 @ X6) | ((X7) = (X4)) | ((X6) != (k1_tarski @ X4)))),
% 7.27/7.44      inference('cnf', [status(esa)], [d1_tarski])).
% 7.27/7.44  thf('21', plain,
% 7.27/7.44      (![X4 : $i, X7 : $i]:
% 7.27/7.44         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 7.27/7.44      inference('simplify', [status(thm)], ['20'])).
% 7.27/7.44  thf('22', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 7.27/7.44          | ((sk_C_2 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['19', '21'])).
% 7.27/7.44  thf('23', plain, (![X32 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X32)) = (X32))),
% 7.27/7.44      inference('demod', [status(thm)], ['10', '11'])).
% 7.27/7.44  thf('24', plain,
% 7.27/7.44      (![X24 : $i, X25 : $i]:
% 7.27/7.44         ((r2_hidden @ 
% 7.27/7.44           (k4_tarski @ (sk_C_2 @ X24 @ X25) @ (sk_D @ X24 @ X25)) @ X25)
% 7.27/7.44          | (r1_tarski @ X25 @ X24)
% 7.27/7.44          | ~ (v1_relat_1 @ X25))),
% 7.27/7.44      inference('cnf', [status(esa)], [d3_relat_1])).
% 7.27/7.44  thf('25', plain,
% 7.27/7.44      (![X29 : $i, X30 : $i, X31 : $i]:
% 7.27/7.44         (~ (r2_hidden @ (k4_tarski @ X29 @ X30) @ X31)
% 7.27/7.44          | (r2_hidden @ X30 @ (k3_relat_1 @ X31))
% 7.27/7.44          | ~ (v1_relat_1 @ X31))),
% 7.27/7.44      inference('cnf', [status(esa)], [t30_relat_1])).
% 7.27/7.44  thf('26', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         (~ (v1_relat_1 @ X0)
% 7.27/7.44          | (r1_tarski @ X0 @ X1)
% 7.27/7.44          | ~ (v1_relat_1 @ X0)
% 7.27/7.44          | (r2_hidden @ (sk_D @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['24', '25'])).
% 7.27/7.44  thf('27', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r2_hidden @ (sk_D @ X1 @ X0) @ (k3_relat_1 @ X0))
% 7.27/7.44          | (r1_tarski @ X0 @ X1)
% 7.27/7.44          | ~ (v1_relat_1 @ X0))),
% 7.27/7.44      inference('simplify', [status(thm)], ['26'])).
% 7.27/7.44  thf('28', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r2_hidden @ (sk_D @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 7.27/7.44          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 7.27/7.44      inference('sup+', [status(thm)], ['23', '27'])).
% 7.27/7.44  thf('29', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 7.27/7.44      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 7.27/7.44  thf('30', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r2_hidden @ (sk_D @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 7.27/7.44      inference('demod', [status(thm)], ['28', '29'])).
% 7.27/7.44  thf('31', plain,
% 7.27/7.44      (![X4 : $i, X7 : $i]:
% 7.27/7.44         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 7.27/7.44      inference('simplify', [status(thm)], ['20'])).
% 7.27/7.44  thf('32', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 7.27/7.44          | ((sk_D @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['30', '31'])).
% 7.27/7.44  thf('33', plain,
% 7.27/7.44      (![X24 : $i, X25 : $i]:
% 7.27/7.44         (~ (r2_hidden @ 
% 7.27/7.44             (k4_tarski @ (sk_C_2 @ X24 @ X25) @ (sk_D @ X24 @ X25)) @ X24)
% 7.27/7.44          | (r1_tarski @ X25 @ X24)
% 7.27/7.44          | ~ (v1_relat_1 @ X25))),
% 7.27/7.44      inference('cnf', [status(esa)], [d3_relat_1])).
% 7.27/7.44  thf('34', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         (~ (r2_hidden @ 
% 7.27/7.44             (k4_tarski @ (sk_C_2 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X0) @ 
% 7.27/7.44             X1)
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 7.27/7.44          | ~ (v1_relat_1 @ (k1_wellord2 @ (k1_tarski @ X0)))
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 7.27/7.44      inference('sup-', [status(thm)], ['32', '33'])).
% 7.27/7.44  thf('35', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 7.27/7.44      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 7.27/7.44  thf('36', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         (~ (r2_hidden @ 
% 7.27/7.44             (k4_tarski @ (sk_C_2 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X0) @ 
% 7.27/7.44             X1)
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 7.27/7.44      inference('demod', [status(thm)], ['34', '35'])).
% 7.27/7.44  thf('37', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 7.27/7.44          | ~ (r2_hidden @ 
% 7.27/7.44               (k4_tarski @ (sk_C_2 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ 
% 7.27/7.44                X0) @ 
% 7.27/7.44               X1))),
% 7.27/7.44      inference('simplify', [status(thm)], ['36'])).
% 7.27/7.44  thf('38', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         (~ (r2_hidden @ (k4_tarski @ X0 @ X0) @ X1)
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 7.27/7.44      inference('sup-', [status(thm)], ['22', '37'])).
% 7.27/7.44  thf('39', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 7.27/7.44          | ~ (r2_hidden @ (k4_tarski @ X0 @ X0) @ X1))),
% 7.27/7.44      inference('simplify', [status(thm)], ['38'])).
% 7.27/7.44  thf('40', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ 
% 7.27/7.44          (k1_tarski @ (k4_tarski @ X0 @ X0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['8', '39'])).
% 7.27/7.44  thf(t71_enumset1, axiom,
% 7.27/7.44    (![A:$i,B:$i,C:$i]:
% 7.27/7.44     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 7.27/7.44  thf('41', plain,
% 7.27/7.44      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.27/7.44         ((k2_enumset1 @ X12 @ X12 @ X13 @ X14)
% 7.27/7.44           = (k1_enumset1 @ X12 @ X13 @ X14))),
% 7.27/7.44      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.27/7.44  thf(t70_enumset1, axiom,
% 7.27/7.44    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 7.27/7.44  thf('42', plain,
% 7.27/7.44      (![X10 : $i, X11 : $i]:
% 7.27/7.44         ((k1_enumset1 @ X10 @ X10 @ X11) = (k2_tarski @ X10 @ X11))),
% 7.27/7.44      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.27/7.44  thf('43', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 7.27/7.44      inference('sup+', [status(thm)], ['41', '42'])).
% 7.27/7.44  thf('44', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 7.27/7.44      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.27/7.44  thf('45', plain,
% 7.27/7.44      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 7.27/7.44      inference('sup+', [status(thm)], ['43', '44'])).
% 7.27/7.44  thf('46', plain,
% 7.27/7.44      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.27/7.44         ((k2_enumset1 @ X12 @ X12 @ X13 @ X14)
% 7.27/7.44           = (k1_enumset1 @ X12 @ X13 @ X14))),
% 7.27/7.44      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.27/7.44  thf(t142_zfmisc_1, axiom,
% 7.27/7.44    (![A:$i,B:$i,C:$i,D:$i]:
% 7.27/7.44     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 7.27/7.44       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 7.27/7.44            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 7.27/7.44            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 7.27/7.44            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 7.27/7.44            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 7.27/7.44            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 7.27/7.44  thf('47', plain,
% 7.27/7.44      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 7.27/7.44         (((X18) = (k1_enumset1 @ X15 @ X16 @ X17))
% 7.27/7.44          | ((X18) = (k2_tarski @ X15 @ X17))
% 7.27/7.44          | ((X18) = (k2_tarski @ X16 @ X17))
% 7.27/7.44          | ((X18) = (k2_tarski @ X15 @ X16))
% 7.27/7.44          | ((X18) = (k1_tarski @ X17))
% 7.27/7.44          | ((X18) = (k1_tarski @ X16))
% 7.27/7.44          | ((X18) = (k1_tarski @ X15))
% 7.27/7.44          | ((X18) = (k1_xboole_0))
% 7.27/7.44          | ~ (r1_tarski @ X18 @ (k1_enumset1 @ X15 @ X16 @ X17)))),
% 7.27/7.44      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 7.27/7.44  thf('48', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.27/7.44         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 7.27/7.44          | ((X3) = (k1_xboole_0))
% 7.27/7.44          | ((X3) = (k1_tarski @ X2))
% 7.27/7.44          | ((X3) = (k1_tarski @ X1))
% 7.27/7.44          | ((X3) = (k1_tarski @ X0))
% 7.27/7.44          | ((X3) = (k2_tarski @ X2 @ X1))
% 7.27/7.44          | ((X3) = (k2_tarski @ X1 @ X0))
% 7.27/7.44          | ((X3) = (k2_tarski @ X2 @ X0))
% 7.27/7.44          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['46', '47'])).
% 7.27/7.44  thf('49', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 7.27/7.44          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 7.27/7.44          | ((X1) = (k2_tarski @ X0 @ X0))
% 7.27/7.44          | ((X1) = (k2_tarski @ X0 @ X0))
% 7.27/7.44          | ((X1) = (k2_tarski @ X0 @ X0))
% 7.27/7.44          | ((X1) = (k1_tarski @ X0))
% 7.27/7.44          | ((X1) = (k1_tarski @ X0))
% 7.27/7.44          | ((X1) = (k1_tarski @ X0))
% 7.27/7.44          | ((X1) = (k1_xboole_0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['45', '48'])).
% 7.27/7.44  thf('50', plain,
% 7.27/7.44      (![X10 : $i, X11 : $i]:
% 7.27/7.44         ((k1_enumset1 @ X10 @ X10 @ X11) = (k2_tarski @ X10 @ X11))),
% 7.27/7.44      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.27/7.44  thf('51', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 7.27/7.44      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.27/7.44  thf('52', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 7.27/7.44      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.27/7.44  thf('53', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 7.27/7.44      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.27/7.44  thf('54', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 7.27/7.44      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.27/7.44  thf('55', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 7.27/7.44          | ((X1) = (k1_tarski @ X0))
% 7.27/7.44          | ((X1) = (k1_tarski @ X0))
% 7.27/7.44          | ((X1) = (k1_tarski @ X0))
% 7.27/7.44          | ((X1) = (k1_tarski @ X0))
% 7.27/7.44          | ((X1) = (k1_tarski @ X0))
% 7.27/7.44          | ((X1) = (k1_tarski @ X0))
% 7.27/7.44          | ((X1) = (k1_tarski @ X0))
% 7.27/7.44          | ((X1) = (k1_xboole_0)))),
% 7.27/7.44      inference('demod', [status(thm)], ['49', '50', '51', '52', '53', '54'])).
% 7.27/7.44  thf('56', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         (((X1) = (k1_xboole_0))
% 7.27/7.44          | ((X1) = (k1_tarski @ X0))
% 7.27/7.44          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 7.27/7.44      inference('simplify', [status(thm)], ['55'])).
% 7.27/7.44  thf('57', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (((k1_wellord2 @ (k1_tarski @ X0))
% 7.27/7.44            = (k1_tarski @ (k4_tarski @ X0 @ X0)))
% 7.27/7.44          | ((k1_wellord2 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['40', '56'])).
% 7.27/7.44  thf('58', plain,
% 7.27/7.44      (((k1_wellord2 @ (k1_tarski @ sk_A))
% 7.27/7.44         != (k1_tarski @ (k4_tarski @ sk_A @ sk_A)))),
% 7.27/7.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.27/7.44  thf('59', plain,
% 7.27/7.44      ((((k1_wellord2 @ (k1_tarski @ sk_A))
% 7.27/7.44          != (k1_wellord2 @ (k1_tarski @ sk_A)))
% 7.27/7.44        | ((k1_wellord2 @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['57', '58'])).
% 7.27/7.44  thf('60', plain, (((k1_wellord2 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 7.27/7.44      inference('simplify', [status(thm)], ['59'])).
% 7.27/7.44  thf('61', plain,
% 7.27/7.44      (((k1_xboole_0) != (k1_tarski @ (k4_tarski @ sk_A @ sk_A)))),
% 7.27/7.44      inference('demod', [status(thm)], ['0', '60'])).
% 7.27/7.44  thf('62', plain, (((k1_wellord2 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 7.27/7.44      inference('simplify', [status(thm)], ['59'])).
% 7.27/7.44  thf('63', plain, (![X32 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X32)) = (X32))),
% 7.27/7.44      inference('demod', [status(thm)], ['10', '11'])).
% 7.27/7.44  thf('64', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_tarski @ sk_A))),
% 7.27/7.44      inference('sup+', [status(thm)], ['62', '63'])).
% 7.27/7.44  thf('65', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 7.27/7.44      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.27/7.44  thf('66', plain,
% 7.27/7.44      (![X20 : $i, X21 : $i, X22 : $i]:
% 7.27/7.44         ((r2_hidden @ X20 @ X21)
% 7.27/7.44          | ~ (r1_tarski @ (k2_tarski @ X20 @ X22) @ X21))),
% 7.27/7.44      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 7.27/7.44  thf('67', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 7.27/7.44      inference('sup-', [status(thm)], ['65', '66'])).
% 7.27/7.44  thf('68', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (~ (r1_tarski @ (k3_relat_1 @ k1_xboole_0) @ X0)
% 7.27/7.44          | (r2_hidden @ sk_A @ X0))),
% 7.27/7.44      inference('sup-', [status(thm)], ['64', '67'])).
% 7.27/7.44  thf('69', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 7.27/7.44      inference('sup+', [status(thm)], ['1', '7'])).
% 7.27/7.44  thf('70', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r2_hidden @ (sk_D @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 7.27/7.44      inference('demod', [status(thm)], ['28', '29'])).
% 7.27/7.44  thf('71', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ 
% 7.27/7.44          (k1_tarski @ (k4_tarski @ X0 @ X0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['8', '39'])).
% 7.27/7.44  thf('72', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.27/7.44         (~ (r2_hidden @ X0 @ X1)
% 7.27/7.44          | (r2_hidden @ X0 @ X2)
% 7.27/7.44          | ~ (r1_tarski @ X1 @ X2))),
% 7.27/7.44      inference('cnf', [status(esa)], [d3_tarski])).
% 7.27/7.44  thf('73', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r2_hidden @ X1 @ (k1_tarski @ (k4_tarski @ X0 @ X0)))
% 7.27/7.44          | ~ (r2_hidden @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))))),
% 7.27/7.44      inference('sup-', [status(thm)], ['71', '72'])).
% 7.27/7.44  thf('74', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r1_tarski @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X1)
% 7.27/7.44          | (r2_hidden @ 
% 7.27/7.44             (sk_D @ X1 @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0)))) @ 
% 7.27/7.44             (k1_tarski @ (k4_tarski @ X0 @ X0))))),
% 7.27/7.44      inference('sup-', [status(thm)], ['70', '73'])).
% 7.27/7.44  thf('75', plain,
% 7.27/7.44      (![X4 : $i, X7 : $i]:
% 7.27/7.44         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 7.27/7.44      inference('simplify', [status(thm)], ['20'])).
% 7.27/7.44  thf('76', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r1_tarski @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X1)
% 7.27/7.44          | ((sk_D @ X1 @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))))
% 7.27/7.44              = (k4_tarski @ X0 @ X0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['74', '75'])).
% 7.27/7.44  thf('77', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r2_hidden @ (sk_C_2 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 7.27/7.44      inference('demod', [status(thm)], ['17', '18'])).
% 7.27/7.44  thf('78', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r2_hidden @ X1 @ (k1_tarski @ (k4_tarski @ X0 @ X0)))
% 7.27/7.44          | ~ (r2_hidden @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))))),
% 7.27/7.44      inference('sup-', [status(thm)], ['71', '72'])).
% 7.27/7.44  thf('79', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r1_tarski @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X1)
% 7.27/7.44          | (r2_hidden @ 
% 7.27/7.44             (sk_C_2 @ X1 @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0)))) @ 
% 7.27/7.44             (k1_tarski @ (k4_tarski @ X0 @ X0))))),
% 7.27/7.44      inference('sup-', [status(thm)], ['77', '78'])).
% 7.27/7.44  thf('80', plain,
% 7.27/7.44      (![X4 : $i, X7 : $i]:
% 7.27/7.44         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 7.27/7.44      inference('simplify', [status(thm)], ['20'])).
% 7.27/7.44  thf('81', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r1_tarski @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X1)
% 7.27/7.44          | ((sk_C_2 @ X1 @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))))
% 7.27/7.44              = (k4_tarski @ X0 @ X0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['79', '80'])).
% 7.27/7.44  thf('82', plain,
% 7.27/7.44      (![X24 : $i, X25 : $i]:
% 7.27/7.44         (~ (r2_hidden @ 
% 7.27/7.44             (k4_tarski @ (sk_C_2 @ X24 @ X25) @ (sk_D @ X24 @ X25)) @ X24)
% 7.27/7.44          | (r1_tarski @ X25 @ X24)
% 7.27/7.44          | ~ (v1_relat_1 @ X25))),
% 7.27/7.44      inference('cnf', [status(esa)], [d3_relat_1])).
% 7.27/7.44  thf('83', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         (~ (r2_hidden @ 
% 7.27/7.44             (k4_tarski @ (k4_tarski @ X0 @ X0) @ 
% 7.27/7.44              (sk_D @ X1 @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))))) @ 
% 7.27/7.44             X1)
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X1)
% 7.27/7.44          | ~ (v1_relat_1 @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))))
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X1))),
% 7.27/7.44      inference('sup-', [status(thm)], ['81', '82'])).
% 7.27/7.44  thf('84', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 7.27/7.44      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 7.27/7.44  thf('85', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         (~ (r2_hidden @ 
% 7.27/7.44             (k4_tarski @ (k4_tarski @ X0 @ X0) @ 
% 7.27/7.44              (sk_D @ X1 @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))))) @ 
% 7.27/7.44             X1)
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X1)
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X1))),
% 7.27/7.44      inference('demod', [status(thm)], ['83', '84'])).
% 7.27/7.44  thf('86', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r1_tarski @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X1)
% 7.27/7.44          | ~ (r2_hidden @ 
% 7.27/7.44               (k4_tarski @ (k4_tarski @ X0 @ X0) @ 
% 7.27/7.44                (sk_D @ X1 @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))))) @ 
% 7.27/7.44               X1))),
% 7.27/7.44      inference('simplify', [status(thm)], ['85'])).
% 7.27/7.44  thf('87', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         (~ (r2_hidden @ 
% 7.27/7.44             (k4_tarski @ (k4_tarski @ X0 @ X0) @ (k4_tarski @ X0 @ X0)) @ X1)
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X1)
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X1))),
% 7.27/7.44      inference('sup-', [status(thm)], ['76', '86'])).
% 7.27/7.44  thf('88', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r1_tarski @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X1)
% 7.27/7.44          | ~ (r2_hidden @ 
% 7.27/7.44               (k4_tarski @ (k4_tarski @ X0 @ X0) @ (k4_tarski @ X0 @ X0)) @ X1))),
% 7.27/7.44      inference('simplify', [status(thm)], ['87'])).
% 7.27/7.44  thf('89', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (r1_tarski @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) @ 
% 7.27/7.44          (k1_tarski @ 
% 7.27/7.44           (k4_tarski @ (k4_tarski @ X0 @ X0) @ (k4_tarski @ X0 @ X0))))),
% 7.27/7.44      inference('sup-', [status(thm)], ['69', '88'])).
% 7.27/7.44  thf('90', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         (((X1) = (k1_xboole_0))
% 7.27/7.44          | ((X1) = (k1_tarski @ X0))
% 7.27/7.44          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 7.27/7.44      inference('simplify', [status(thm)], ['55'])).
% 7.27/7.44  thf('91', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (((k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0)))
% 7.27/7.44            = (k1_tarski @ 
% 7.27/7.44               (k4_tarski @ (k4_tarski @ X0 @ X0) @ (k4_tarski @ X0 @ X0))))
% 7.27/7.44          | ((k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) = (k1_xboole_0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['89', '90'])).
% 7.27/7.44  thf('92', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (((k1_wellord2 @ (k1_tarski @ X0))
% 7.27/7.44            = (k1_tarski @ (k4_tarski @ X0 @ X0)))
% 7.27/7.44          | ((k1_wellord2 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['40', '56'])).
% 7.27/7.44  thf('93', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (((k1_wellord2 @ (k1_tarski @ (k4_tarski @ X0 @ X0)))
% 7.27/7.44            = (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))))
% 7.27/7.44          | ((k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) = (k1_xboole_0))
% 7.27/7.44          | ((k1_wellord2 @ (k1_tarski @ (k4_tarski @ X0 @ X0)))
% 7.27/7.44              = (k1_xboole_0)))),
% 7.27/7.44      inference('sup+', [status(thm)], ['91', '92'])).
% 7.27/7.44  thf('94', plain, (![X32 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X32)) = (X32))),
% 7.27/7.44      inference('demod', [status(thm)], ['10', '11'])).
% 7.27/7.44  thf('95', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (((k3_relat_1 @ (k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))))
% 7.27/7.44            = (k1_tarski @ (k4_tarski @ X0 @ X0)))
% 7.27/7.44          | ((k1_wellord2 @ (k1_tarski @ (k4_tarski @ X0 @ X0)))
% 7.27/7.44              = (k1_xboole_0))
% 7.27/7.44          | ((k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) = (k1_xboole_0)))),
% 7.27/7.44      inference('sup+', [status(thm)], ['93', '94'])).
% 7.27/7.44  thf('96', plain, (![X32 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X32)) = (X32))),
% 7.27/7.44      inference('demod', [status(thm)], ['10', '11'])).
% 7.27/7.44  thf('97', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (((k1_wellord2 @ (k1_tarski @ X0))
% 7.27/7.44            = (k1_tarski @ (k4_tarski @ X0 @ X0)))
% 7.27/7.44          | ((k1_wellord2 @ (k1_tarski @ (k4_tarski @ X0 @ X0)))
% 7.27/7.44              = (k1_xboole_0))
% 7.27/7.44          | ((k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) = (k1_xboole_0)))),
% 7.27/7.44      inference('demod', [status(thm)], ['95', '96'])).
% 7.27/7.44  thf('98', plain, (![X32 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X32)) = (X32))),
% 7.27/7.44      inference('demod', [status(thm)], ['10', '11'])).
% 7.27/7.44  thf('99', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (((k3_relat_1 @ k1_xboole_0) = (k1_tarski @ (k4_tarski @ X0 @ X0)))
% 7.27/7.44          | ((k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) = (k1_xboole_0))
% 7.27/7.44          | ((k1_wellord2 @ (k1_tarski @ X0))
% 7.27/7.44              = (k1_tarski @ (k4_tarski @ X0 @ X0))))),
% 7.27/7.44      inference('sup+', [status(thm)], ['97', '98'])).
% 7.27/7.44  thf('100', plain,
% 7.27/7.44      (((k1_xboole_0) != (k1_tarski @ (k4_tarski @ sk_A @ sk_A)))),
% 7.27/7.44      inference('demod', [status(thm)], ['0', '60'])).
% 7.27/7.44  thf('101', plain,
% 7.27/7.44      ((((k1_xboole_0) != (k1_wellord2 @ (k1_tarski @ sk_A)))
% 7.27/7.44        | ((k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ sk_A))) = (k1_xboole_0))
% 7.27/7.44        | ((k3_relat_1 @ k1_xboole_0) = (k1_tarski @ (k4_tarski @ sk_A @ sk_A))))),
% 7.27/7.44      inference('sup-', [status(thm)], ['99', '100'])).
% 7.27/7.44  thf('102', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_tarski @ sk_A))),
% 7.27/7.44      inference('sup+', [status(thm)], ['62', '63'])).
% 7.27/7.44  thf('103', plain, (((k1_wellord2 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 7.27/7.44      inference('simplify', [status(thm)], ['59'])).
% 7.27/7.44  thf('104', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_tarski @ sk_A))),
% 7.27/7.44      inference('sup+', [status(thm)], ['62', '63'])).
% 7.27/7.44  thf('105', plain,
% 7.27/7.44      (((k1_wellord2 @ (k3_relat_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 7.27/7.44      inference('demod', [status(thm)], ['103', '104'])).
% 7.27/7.44  thf('106', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_tarski @ sk_A))),
% 7.27/7.44      inference('sup+', [status(thm)], ['62', '63'])).
% 7.27/7.44  thf('107', plain,
% 7.27/7.44      (((k1_wellord2 @ (k3_relat_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 7.27/7.44      inference('demod', [status(thm)], ['103', '104'])).
% 7.27/7.44  thf('108', plain,
% 7.27/7.44      ((((k1_xboole_0) != (k1_xboole_0))
% 7.27/7.44        | ((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0))
% 7.27/7.44        | ((k3_relat_1 @ k1_xboole_0) = (k1_tarski @ (k4_tarski @ sk_A @ sk_A))))),
% 7.27/7.44      inference('demod', [status(thm)], ['101', '102', '105', '106', '107'])).
% 7.27/7.44  thf('109', plain,
% 7.27/7.44      ((((k3_relat_1 @ k1_xboole_0) = (k1_tarski @ (k4_tarski @ sk_A @ sk_A)))
% 7.27/7.44        | ((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0)))),
% 7.27/7.44      inference('simplify', [status(thm)], ['108'])).
% 7.27/7.44  thf('110', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 7.27/7.44      inference('sup+', [status(thm)], ['1', '7'])).
% 7.27/7.44  thf('111', plain,
% 7.27/7.44      (((r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ (k3_relat_1 @ k1_xboole_0))
% 7.27/7.44        | ((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0)))),
% 7.27/7.44      inference('sup+', [status(thm)], ['109', '110'])).
% 7.27/7.44  thf('112', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_tarski @ sk_A))),
% 7.27/7.44      inference('sup+', [status(thm)], ['62', '63'])).
% 7.27/7.44  thf('113', plain,
% 7.27/7.44      (![X4 : $i, X7 : $i]:
% 7.27/7.44         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 7.27/7.44      inference('simplify', [status(thm)], ['20'])).
% 7.27/7.44  thf('114', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (~ (r2_hidden @ X0 @ (k3_relat_1 @ k1_xboole_0)) | ((X0) = (sk_A)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['112', '113'])).
% 7.27/7.44  thf('115', plain,
% 7.27/7.44      ((((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0))
% 7.27/7.44        | ((k4_tarski @ sk_A @ sk_A) = (sk_A)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['111', '114'])).
% 7.27/7.44  thf('116', plain,
% 7.27/7.44      ((((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0))
% 7.27/7.44        | ((k4_tarski @ sk_A @ sk_A) = (sk_A)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['111', '114'])).
% 7.27/7.44  thf('117', plain,
% 7.27/7.44      ((((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0))
% 7.27/7.44        | ((k4_tarski @ sk_A @ sk_A) = (sk_A)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['111', '114'])).
% 7.27/7.44  thf('118', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (((k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0)))
% 7.27/7.44            = (k1_tarski @ 
% 7.27/7.44               (k4_tarski @ (k4_tarski @ X0 @ X0) @ (k4_tarski @ X0 @ X0))))
% 7.27/7.44          | ((k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ X0))) = (k1_xboole_0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['89', '90'])).
% 7.27/7.44  thf('119', plain,
% 7.27/7.44      ((((k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ sk_A)))
% 7.27/7.44          = (k1_tarski @ (k4_tarski @ (k4_tarski @ sk_A @ sk_A) @ sk_A)))
% 7.27/7.44        | ((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0))
% 7.27/7.44        | ((k1_wellord2 @ (k1_wellord2 @ (k1_tarski @ sk_A))) = (k1_xboole_0)))),
% 7.27/7.44      inference('sup+', [status(thm)], ['117', '118'])).
% 7.27/7.44  thf('120', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_tarski @ sk_A))),
% 7.27/7.44      inference('sup+', [status(thm)], ['62', '63'])).
% 7.27/7.44  thf('121', plain,
% 7.27/7.44      (((k1_wellord2 @ (k3_relat_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 7.27/7.44      inference('demod', [status(thm)], ['103', '104'])).
% 7.27/7.44  thf('122', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_tarski @ sk_A))),
% 7.27/7.44      inference('sup+', [status(thm)], ['62', '63'])).
% 7.27/7.44  thf('123', plain,
% 7.27/7.44      (((k1_wellord2 @ (k3_relat_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 7.27/7.44      inference('demod', [status(thm)], ['103', '104'])).
% 7.27/7.44  thf('124', plain,
% 7.27/7.44      ((((k1_wellord2 @ k1_xboole_0)
% 7.27/7.44          = (k1_tarski @ (k4_tarski @ (k4_tarski @ sk_A @ sk_A) @ sk_A)))
% 7.27/7.44        | ((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0))
% 7.27/7.44        | ((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0)))),
% 7.27/7.44      inference('demod', [status(thm)], ['119', '120', '121', '122', '123'])).
% 7.27/7.44  thf('125', plain,
% 7.27/7.44      ((((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0))
% 7.27/7.44        | ((k1_wellord2 @ k1_xboole_0)
% 7.27/7.44            = (k1_tarski @ (k4_tarski @ (k4_tarski @ sk_A @ sk_A) @ sk_A))))),
% 7.27/7.44      inference('simplify', [status(thm)], ['124'])).
% 7.27/7.44  thf('126', plain,
% 7.27/7.44      ((((k1_wellord2 @ k1_xboole_0) = (k1_tarski @ (k4_tarski @ sk_A @ sk_A)))
% 7.27/7.44        | ((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0))
% 7.27/7.44        | ((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0)))),
% 7.27/7.44      inference('sup+', [status(thm)], ['116', '125'])).
% 7.27/7.44  thf('127', plain,
% 7.27/7.44      ((((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0))
% 7.27/7.44        | ((k1_wellord2 @ k1_xboole_0)
% 7.27/7.44            = (k1_tarski @ (k4_tarski @ sk_A @ sk_A))))),
% 7.27/7.44      inference('simplify', [status(thm)], ['126'])).
% 7.27/7.44  thf('128', plain,
% 7.27/7.44      ((((k1_wellord2 @ k1_xboole_0) = (k1_tarski @ sk_A))
% 7.27/7.44        | ((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0))
% 7.27/7.44        | ((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0)))),
% 7.27/7.44      inference('sup+', [status(thm)], ['115', '127'])).
% 7.27/7.44  thf('129', plain,
% 7.27/7.44      ((((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0))
% 7.27/7.44        | ((k1_wellord2 @ k1_xboole_0) = (k1_tarski @ sk_A)))),
% 7.27/7.44      inference('simplify', [status(thm)], ['128'])).
% 7.27/7.44  thf('130', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 7.27/7.44      inference('sup-', [status(thm)], ['65', '66'])).
% 7.27/7.44  thf('131', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (~ (r1_tarski @ (k1_wellord2 @ k1_xboole_0) @ X0)
% 7.27/7.44          | ((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0))
% 7.27/7.44          | (r2_hidden @ sk_A @ X0))),
% 7.27/7.44      inference('sup-', [status(thm)], ['129', '130'])).
% 7.27/7.44  thf('132', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r2_hidden @ (sk_D @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 7.27/7.44      inference('demod', [status(thm)], ['28', '29'])).
% 7.27/7.44  thf('133', plain,
% 7.27/7.44      (![X1 : $i, X3 : $i]:
% 7.27/7.44         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.27/7.44      inference('cnf', [status(esa)], [d3_tarski])).
% 7.27/7.44  thf('134', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 7.27/7.44      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.27/7.44  thf('135', plain,
% 7.27/7.44      (![X10 : $i, X11 : $i]:
% 7.27/7.44         ((k1_enumset1 @ X10 @ X10 @ X11) = (k2_tarski @ X10 @ X11))),
% 7.27/7.44      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.27/7.44  thf('136', plain,
% 7.27/7.44      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 7.27/7.44         ((r1_tarski @ X19 @ (k1_enumset1 @ X15 @ X16 @ X17))
% 7.27/7.44          | ((X19) != (k1_xboole_0)))),
% 7.27/7.44      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 7.27/7.44  thf('137', plain,
% 7.27/7.44      (![X15 : $i, X16 : $i, X17 : $i]:
% 7.27/7.44         (r1_tarski @ k1_xboole_0 @ (k1_enumset1 @ X15 @ X16 @ X17))),
% 7.27/7.44      inference('simplify', [status(thm)], ['136'])).
% 7.27/7.44  thf('138', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]: (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 7.27/7.44      inference('sup+', [status(thm)], ['135', '137'])).
% 7.27/7.44  thf('139', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 7.27/7.44      inference('sup+', [status(thm)], ['134', '138'])).
% 7.27/7.44  thf('140', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.27/7.44         (~ (r2_hidden @ X0 @ X1)
% 7.27/7.44          | (r2_hidden @ X0 @ X2)
% 7.27/7.44          | ~ (r1_tarski @ X1 @ X2))),
% 7.27/7.44      inference('cnf', [status(esa)], [d3_tarski])).
% 7.27/7.44  thf('141', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 7.27/7.44          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 7.27/7.44      inference('sup-', [status(thm)], ['139', '140'])).
% 7.27/7.44  thf('142', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r1_tarski @ k1_xboole_0 @ X0)
% 7.27/7.44          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ (k1_tarski @ X1)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['133', '141'])).
% 7.27/7.44  thf('143', plain,
% 7.27/7.44      (![X4 : $i, X7 : $i]:
% 7.27/7.44         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 7.27/7.44      inference('simplify', [status(thm)], ['20'])).
% 7.27/7.44  thf('144', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r1_tarski @ k1_xboole_0 @ X1) | ((sk_C @ X1 @ k1_xboole_0) = (X0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['142', '143'])).
% 7.27/7.44  thf('145', plain,
% 7.27/7.44      (((k1_wellord2 @ (k1_tarski @ sk_A))
% 7.27/7.44         != (k1_tarski @ (k4_tarski @ sk_A @ sk_A)))),
% 7.27/7.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.27/7.44  thf('146', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (((k1_wellord2 @ (k1_tarski @ sk_A)) != (sk_C @ X0 @ k1_xboole_0))
% 7.27/7.44          | (r1_tarski @ k1_xboole_0 @ X0))),
% 7.27/7.44      inference('sup-', [status(thm)], ['144', '145'])).
% 7.27/7.44  thf('147', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r1_tarski @ k1_xboole_0 @ X1) | ((sk_C @ X1 @ k1_xboole_0) = (X0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['142', '143'])).
% 7.27/7.44  thf('148', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 7.27/7.44      inference('clc', [status(thm)], ['146', '147'])).
% 7.27/7.44  thf('149', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.27/7.44         (~ (r2_hidden @ X0 @ X1)
% 7.27/7.44          | (r2_hidden @ X0 @ X2)
% 7.27/7.44          | ~ (r1_tarski @ X1 @ X2))),
% 7.27/7.44      inference('cnf', [status(esa)], [d3_tarski])).
% 7.27/7.44  thf('150', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 7.27/7.44      inference('sup-', [status(thm)], ['148', '149'])).
% 7.27/7.44  thf('151', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r1_tarski @ (k1_wellord2 @ k1_xboole_0) @ X0)
% 7.27/7.44          | (r2_hidden @ (sk_D @ X0 @ (k1_wellord2 @ k1_xboole_0)) @ X1))),
% 7.27/7.44      inference('sup-', [status(thm)], ['132', '150'])).
% 7.27/7.44  thf('152', plain,
% 7.27/7.44      (![X4 : $i, X7 : $i]:
% 7.27/7.44         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 7.27/7.44      inference('simplify', [status(thm)], ['20'])).
% 7.27/7.44  thf('153', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r1_tarski @ (k1_wellord2 @ k1_xboole_0) @ X1)
% 7.27/7.44          | ((sk_D @ X1 @ (k1_wellord2 @ k1_xboole_0)) = (X0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['151', '152'])).
% 7.27/7.44  thf('154', plain,
% 7.27/7.44      (((k1_wellord2 @ (k1_tarski @ sk_A))
% 7.27/7.44         != (k1_tarski @ (k4_tarski @ sk_A @ sk_A)))),
% 7.27/7.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.27/7.44  thf('155', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (((k1_wellord2 @ (k1_tarski @ sk_A))
% 7.27/7.44            != (sk_D @ X0 @ (k1_wellord2 @ k1_xboole_0)))
% 7.27/7.44          | (r1_tarski @ (k1_wellord2 @ k1_xboole_0) @ X0))),
% 7.27/7.44      inference('sup-', [status(thm)], ['153', '154'])).
% 7.27/7.44  thf('156', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         ((r1_tarski @ (k1_wellord2 @ k1_xboole_0) @ X1)
% 7.27/7.44          | ((sk_D @ X1 @ (k1_wellord2 @ k1_xboole_0)) = (X0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['151', '152'])).
% 7.27/7.44  thf('157', plain,
% 7.27/7.44      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ k1_xboole_0) @ X0)),
% 7.27/7.44      inference('clc', [status(thm)], ['155', '156'])).
% 7.27/7.44  thf('158', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0))
% 7.27/7.44          | (r2_hidden @ sk_A @ X0))),
% 7.27/7.44      inference('demod', [status(thm)], ['131', '157'])).
% 7.27/7.44  thf('159', plain,
% 7.27/7.44      (![X4 : $i, X7 : $i]:
% 7.27/7.44         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 7.27/7.44      inference('simplify', [status(thm)], ['20'])).
% 7.27/7.44  thf('160', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0)) | ((sk_A) = (X0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['158', '159'])).
% 7.27/7.44  thf('161', plain,
% 7.27/7.44      (![X0 : $i]:
% 7.27/7.44         (((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0)) | ((sk_A) = (X0)))),
% 7.27/7.44      inference('sup-', [status(thm)], ['158', '159'])).
% 7.27/7.44  thf('162', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         (((X0) = (X1))
% 7.27/7.44          | ((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0))
% 7.27/7.44          | ((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0)))),
% 7.27/7.44      inference('sup+', [status(thm)], ['160', '161'])).
% 7.27/7.44  thf('163', plain,
% 7.27/7.44      (![X0 : $i, X1 : $i]:
% 7.27/7.44         (((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0)) | ((X0) = (X1)))),
% 7.27/7.44      inference('simplify', [status(thm)], ['162'])).
% 7.27/7.44  thf('164', plain, (((k1_wellord2 @ k1_xboole_0) = (k1_xboole_0))),
% 7.27/7.44      inference('condensation', [status(thm)], ['163'])).
% 7.27/7.44  thf('165', plain,
% 7.27/7.44      (![X32 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X32)) = (X32))),
% 7.27/7.44      inference('demod', [status(thm)], ['10', '11'])).
% 7.27/7.44  thf('166', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 7.27/7.44      inference('sup+', [status(thm)], ['164', '165'])).
% 7.27/7.44  thf('167', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 7.27/7.44      inference('clc', [status(thm)], ['146', '147'])).
% 7.27/7.44  thf('168', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 7.27/7.44      inference('demod', [status(thm)], ['68', '166', '167'])).
% 7.27/7.44  thf('169', plain,
% 7.27/7.44      (![X4 : $i, X7 : $i]:
% 7.27/7.44         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 7.27/7.44      inference('simplify', [status(thm)], ['20'])).
% 7.27/7.44  thf('170', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 7.27/7.44      inference('sup-', [status(thm)], ['168', '169'])).
% 7.27/7.44  thf('171', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_tarski @ sk_A))),
% 7.27/7.44      inference('sup+', [status(thm)], ['62', '63'])).
% 7.27/7.44  thf('172', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 7.27/7.44      inference('sup+', [status(thm)], ['164', '165'])).
% 7.27/7.44  thf('173', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 7.27/7.44      inference('demod', [status(thm)], ['171', '172'])).
% 7.27/7.44  thf('174', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 7.27/7.44      inference('demod', [status(thm)], ['61', '170', '173'])).
% 7.27/7.44  thf('175', plain, ($false), inference('simplify', [status(thm)], ['174'])).
% 7.27/7.44  
% 7.27/7.44  % SZS output end Refutation
% 7.27/7.44  
% 7.27/7.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
