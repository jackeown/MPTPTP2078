%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OHy3gctueY

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:31 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  178 (1452 expanded)
%              Number of leaves         :   28 ( 450 expanded)
%              Depth                    :   46
%              Number of atoms          : 1491 (14627 expanded)
%              Number of equality atoms :   89 (1007 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X25: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X25 ) )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ( r2_hidden @ X4 @ X3 )
      | ( X4 = X3 )
      | ( r2_hidden @ X3 @ X4 )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('2',plain,(
    ! [X25: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X25 ) )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('3',plain,(
    ! [X25: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X25 ) )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t50_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_xboole_0 @ A @ B )
              & ( A != B )
              & ~ ( r2_xboole_0 @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ( r2_xboole_0 @ X6 @ X5 )
      | ( X6 = X5 )
      | ( r2_xboole_0 @ X5 @ X6 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t50_ordinal1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('7',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X27 ) @ X26 )
        = ( k1_wellord2 @ X26 ) )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

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

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19
       != ( k1_wellord2 @ X18 ) )
      | ( ( k3_relat_1 @ X19 )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('11',plain,(
    ! [X18: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X18 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X18 ) )
        = X18 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('12',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('13',plain,(
    ! [X18: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t30_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) )
        = A ) ) )).

thf('14',plain,(
    ! [X10: $i] :
      ( ( ( k2_wellord1 @ X10 @ ( k3_relat_1 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t30_wellord1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
        = ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
      = ( k1_wellord2 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X7 @ X9 ) @ X8 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X7 @ X8 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) @ X0 )
        = ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_wellord1 @ ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) @ X0 )
      = ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ( r2_hidden @ X4 @ X3 )
      | ( X4 = X3 )
      | ( r2_hidden @ X3 @ X4 )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('26',plain,(
    ! [X25: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X25 ) )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t11_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_wellord2])).

thf('27',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ( r2_hidden @ X4 @ X3 )
      | ( X4 = X3 )
      | ( r2_hidden @ X3 @ X4 )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ( X24
        = ( k1_wellord1 @ ( k1_wellord2 @ X23 ) @ X24 ) )
      | ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( v3_ordinal1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_wellord1 @ X16 )
      | ~ ( r4_wellord1 @ X16 @ ( k2_wellord1 @ X16 @ ( k1_wellord1 @ X16 @ X17 ) ) )
      | ~ ( r2_hidden @ X17 @ ( k3_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('36',plain,(
    ! [X18: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','39'])).

thf('41',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','45'])).

thf('47',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','48'])).

thf('50',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ( X24
        = ( k1_wellord1 @ ( k1_wellord2 @ X23 ) @ X24 ) )
      | ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( v3_ordinal1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('57',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_wellord1 @ X16 )
      | ~ ( r4_wellord1 @ X16 @ ( k2_wellord1 @ X16 @ ( k1_wellord1 @ X16 @ X17 ) ) )
      | ~ ( r2_hidden @ X17 @ ( k3_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('62',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ( r2_xboole_0 @ sk_A @ sk_B )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B ) ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('64',plain,(
    ! [X18: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('65',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ( r2_xboole_0 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_B ) )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['24','65'])).

thf('67',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('69',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r4_wellord1 @ X11 @ X12 )
      | ~ ( r4_wellord1 @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('72',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('73',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf(t52_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( r4_wellord1 @ A @ B )
                  & ( r4_wellord1 @ B @ C ) )
               => ( r4_wellord1 @ A @ C ) ) ) ) ) )).

thf('74',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( r4_wellord1 @ X14 @ X13 )
      | ~ ( r4_wellord1 @ X13 @ X15 )
      | ( r4_wellord1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t52_wellord1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('77',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','78'])).

thf('80',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('81',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['66','81','82','83'])).

thf('85',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ( sk_B = sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('89',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','89'])).

thf('91',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('94',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X27 ) @ X26 )
        = ( k1_wellord2 @ X26 ) )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('96',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X10: $i] :
      ( ( ( k2_wellord1 @ X10 @ ( k3_relat_1 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t30_wellord1])).

thf('98',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X7 @ X9 ) @ X8 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X7 @ X8 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_wellord1 @ X0 @ X1 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ X0 @ X1 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
      = ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['96','100'])).

thf('102',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('103',plain,(
    ! [X18: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('104',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('105',plain,
    ( ( k1_wellord2 @ sk_A )
    = ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['101','102','103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('107',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('109',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( r4_wellord1 @ X14 @ X13 )
      | ~ ( r4_wellord1 @ X13 @ X15 )
      | ( r4_wellord1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t52_wellord1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('113',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','114'])).

thf('116',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('117',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['107','117','118','119'])).

thf('121',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','122'])).

thf('124',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','125'])).

thf('127',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ( X24
        = ( k1_wellord1 @ ( k1_wellord2 @ X23 ) @ X24 ) )
      | ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( v3_ordinal1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('134',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_wellord1 @ X16 )
      | ~ ( r4_wellord1 @ X16 @ ( k2_wellord1 @ X16 @ ( k1_wellord1 @ X16 @ X17 ) ) )
      | ~ ( r2_hidden @ X17 @ ( k3_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('139',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B ) ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('141',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('142',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('143',plain,(
    ! [X18: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('144',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['130','131'])).

thf('145',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143','144'])).

thf('146',plain,(
    ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','145'])).

thf('147',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    $false ),
    inference(demod,[status(thm)],['146','147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OHy3gctueY
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:42:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 120 iterations in 0.107s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.39/0.57  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.39/0.57  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.39/0.57  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.39/0.57  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.39/0.57  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.39/0.57  thf(t7_wellord2, axiom,
% 0.39/0.57    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      (![X25 : $i]:
% 0.39/0.57         ((v2_wellord1 @ (k1_wellord2 @ X25)) | ~ (v3_ordinal1 @ X25))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.39/0.57  thf(t24_ordinal1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v3_ordinal1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.39/0.57           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.39/0.57                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      (![X3 : $i, X4 : $i]:
% 0.39/0.57         (~ (v3_ordinal1 @ X3)
% 0.39/0.57          | (r2_hidden @ X4 @ X3)
% 0.39/0.57          | ((X4) = (X3))
% 0.39/0.57          | (r2_hidden @ X3 @ X4)
% 0.39/0.57          | ~ (v3_ordinal1 @ X4))),
% 0.39/0.57      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (![X25 : $i]:
% 0.39/0.57         ((v2_wellord1 @ (k1_wellord2 @ X25)) | ~ (v3_ordinal1 @ X25))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X25 : $i]:
% 0.39/0.57         ((v2_wellord1 @ (k1_wellord2 @ X25)) | ~ (v3_ordinal1 @ X25))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.39/0.57  thf(t50_ordinal1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v3_ordinal1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.39/0.57           ( ~( ( ~( r2_xboole_0 @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.39/0.57                ( ~( r2_xboole_0 @ B @ A ) ) ) ) ) ) ))).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X5 : $i, X6 : $i]:
% 0.39/0.57         (~ (v3_ordinal1 @ X5)
% 0.39/0.57          | (r2_xboole_0 @ X6 @ X5)
% 0.39/0.57          | ((X6) = (X5))
% 0.39/0.57          | (r2_xboole_0 @ X5 @ X6)
% 0.39/0.57          | ~ (v3_ordinal1 @ X6))),
% 0.39/0.57      inference('cnf', [status(esa)], [t50_ordinal1])).
% 0.39/0.57  thf(d8_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.39/0.57       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v3_ordinal1 @ X1)
% 0.39/0.57          | (r2_xboole_0 @ X0 @ X1)
% 0.39/0.57          | ((X1) = (X0))
% 0.39/0.57          | ~ (v3_ordinal1 @ X0)
% 0.39/0.57          | (r1_tarski @ X1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.57  thf(t8_wellord2, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) =>
% 0.39/0.57       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X26 : $i, X27 : $i]:
% 0.39/0.57         (((k2_wellord1 @ (k1_wellord2 @ X27) @ X26) = (k1_wellord2 @ X26))
% 0.39/0.57          | ~ (r1_tarski @ X26 @ X27))),
% 0.39/0.57      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v3_ordinal1 @ X0)
% 0.39/0.57          | ((X1) = (X0))
% 0.39/0.57          | (r2_xboole_0 @ X0 @ X1)
% 0.39/0.57          | ~ (v3_ordinal1 @ X1)
% 0.39/0.57          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v3_ordinal1 @ X0)
% 0.39/0.57          | ((X1) = (X0))
% 0.39/0.57          | (r2_xboole_0 @ X0 @ X1)
% 0.39/0.57          | ~ (v3_ordinal1 @ X1)
% 0.39/0.57          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf(d1_wellord2, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.39/0.57         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.39/0.57           ( ![C:$i,D:$i]:
% 0.39/0.57             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.39/0.57               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.39/0.57                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (![X18 : $i, X19 : $i]:
% 0.39/0.57         (((X19) != (k1_wellord2 @ X18))
% 0.39/0.57          | ((k3_relat_1 @ X19) = (X18))
% 0.39/0.57          | ~ (v1_relat_1 @ X19))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X18 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ (k1_wellord2 @ X18))
% 0.39/0.57          | ((k3_relat_1 @ (k1_wellord2 @ X18)) = (X18)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['10'])).
% 0.39/0.57  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.39/0.57  thf('12', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.57  thf('13', plain, (![X18 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X18)) = (X18))),
% 0.39/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf(t30_wellord1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ))).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X10 : $i]:
% 0.39/0.57         (((k2_wellord1 @ X10 @ (k3_relat_1 @ X10)) = (X10))
% 0.39/0.57          | ~ (v1_relat_1 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t30_wellord1])).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k2_wellord1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))
% 0.39/0.57          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.39/0.57  thf('16', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((k2_wellord1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.39/0.57  thf(t27_wellord1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ C ) =>
% 0.39/0.57       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.39/0.57         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.57         (((k2_wellord1 @ (k2_wellord1 @ X7 @ X9) @ X8)
% 0.39/0.57            = (k2_wellord1 @ (k2_wellord1 @ X7 @ X8) @ X9))
% 0.39/0.57          | ~ (v1_relat_1 @ X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k2_wellord1 @ (k2_wellord1 @ (k1_wellord2 @ X0) @ X1) @ X0)
% 0.39/0.57            = (k2_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.39/0.57          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['17', '18'])).
% 0.39/0.57  thf('20', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k2_wellord1 @ (k2_wellord1 @ (k1_wellord2 @ X0) @ X1) @ X0)
% 0.39/0.57           = (k2_wellord1 @ (k1_wellord2 @ X0) @ X1))),
% 0.39/0.57      inference('demod', [status(thm)], ['19', '20'])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k2_wellord1 @ (k1_wellord2 @ X0) @ X1)
% 0.39/0.57            = (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.39/0.57          | ~ (v3_ordinal1 @ X0)
% 0.39/0.57          | (r2_xboole_0 @ X1 @ X0)
% 0.39/0.57          | ((X0) = (X1))
% 0.39/0.57          | ~ (v3_ordinal1 @ X1))),
% 0.39/0.57      inference('sup+', [status(thm)], ['9', '21'])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X0))
% 0.39/0.57          | ~ (v3_ordinal1 @ X0)
% 0.39/0.57          | (r2_xboole_0 @ X1 @ X0)
% 0.39/0.57          | ((X0) = (X1))
% 0.39/0.57          | ~ (v3_ordinal1 @ X1)
% 0.39/0.57          | ~ (v3_ordinal1 @ X1)
% 0.39/0.57          | ((X0) = (X1))
% 0.39/0.57          | (r2_xboole_0 @ X1 @ X0)
% 0.39/0.57          | ~ (v3_ordinal1 @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['8', '22'])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v3_ordinal1 @ X1)
% 0.39/0.57          | ((X0) = (X1))
% 0.39/0.57          | (r2_xboole_0 @ X1 @ X0)
% 0.39/0.57          | ~ (v3_ordinal1 @ X0)
% 0.39/0.57          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X0)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['23'])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X3 : $i, X4 : $i]:
% 0.39/0.57         (~ (v3_ordinal1 @ X3)
% 0.39/0.57          | (r2_hidden @ X4 @ X3)
% 0.39/0.57          | ((X4) = (X3))
% 0.39/0.57          | (r2_hidden @ X3 @ X4)
% 0.39/0.57          | ~ (v3_ordinal1 @ X4))),
% 0.39/0.57      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (![X25 : $i]:
% 0.39/0.57         ((v2_wellord1 @ (k1_wellord2 @ X25)) | ~ (v3_ordinal1 @ X25))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.39/0.57  thf(t11_wellord2, conjecture,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v3_ordinal1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.39/0.57           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.39/0.57             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i]:
% 0.39/0.57        ( ( v3_ordinal1 @ A ) =>
% 0.39/0.57          ( ![B:$i]:
% 0.39/0.57            ( ( v3_ordinal1 @ B ) =>
% 0.39/0.57              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.39/0.57                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v3_ordinal1 @ X0)
% 0.39/0.57          | ((X1) = (X0))
% 0.39/0.57          | (r2_xboole_0 @ X0 @ X1)
% 0.39/0.57          | ~ (v3_ordinal1 @ X1)
% 0.39/0.57          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X3 : $i, X4 : $i]:
% 0.39/0.57         (~ (v3_ordinal1 @ X3)
% 0.39/0.57          | (r2_hidden @ X4 @ X3)
% 0.39/0.57          | ((X4) = (X3))
% 0.39/0.57          | (r2_hidden @ X3 @ X4)
% 0.39/0.57          | ~ (v3_ordinal1 @ X4))),
% 0.39/0.57      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.39/0.57  thf(t10_wellord2, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v3_ordinal1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.39/0.57           ( ( r2_hidden @ A @ B ) =>
% 0.39/0.57             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      (![X23 : $i, X24 : $i]:
% 0.39/0.57         (~ (v3_ordinal1 @ X23)
% 0.39/0.57          | ((X24) = (k1_wellord1 @ (k1_wellord2 @ X23) @ X24))
% 0.39/0.57          | ~ (r2_hidden @ X24 @ X23)
% 0.39/0.57          | ~ (v3_ordinal1 @ X24))),
% 0.39/0.57      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v3_ordinal1 @ X1)
% 0.39/0.57          | (r2_hidden @ X0 @ X1)
% 0.39/0.57          | ((X1) = (X0))
% 0.39/0.57          | ~ (v3_ordinal1 @ X0)
% 0.39/0.57          | ~ (v3_ordinal1 @ X1)
% 0.39/0.57          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.39/0.57          | ~ (v3_ordinal1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.39/0.57          | ~ (v3_ordinal1 @ X0)
% 0.39/0.57          | ((X1) = (X0))
% 0.39/0.57          | (r2_hidden @ X0 @ X1)
% 0.39/0.57          | ~ (v3_ordinal1 @ X1))),
% 0.39/0.57      inference('simplify', [status(thm)], ['31'])).
% 0.39/0.57  thf(t57_wellord1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ( v2_wellord1 @ A ) =>
% 0.39/0.57         ( ![B:$i]:
% 0.39/0.57           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.39/0.57                ( r4_wellord1 @
% 0.39/0.57                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      (![X16 : $i, X17 : $i]:
% 0.39/0.57         (~ (v2_wellord1 @ X16)
% 0.39/0.57          | ~ (r4_wellord1 @ X16 @ 
% 0.39/0.57               (k2_wellord1 @ X16 @ (k1_wellord1 @ X16 @ X17)))
% 0.39/0.57          | ~ (r2_hidden @ X17 @ (k3_relat_1 @ X16))
% 0.39/0.57          | ~ (v1_relat_1 @ X16))),
% 0.39/0.57      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.39/0.57             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.39/0.57          | ~ (v3_ordinal1 @ X0)
% 0.39/0.57          | (r2_hidden @ X1 @ X0)
% 0.39/0.57          | ((X0) = (X1))
% 0.39/0.57          | ~ (v3_ordinal1 @ X1)
% 0.39/0.57          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.39/0.57          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.39/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.57  thf('35', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.57  thf('36', plain, (![X18 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X18)) = (X18))),
% 0.39/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.39/0.57             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.39/0.57          | ~ (v3_ordinal1 @ X0)
% 0.39/0.57          | (r2_hidden @ X1 @ X0)
% 0.39/0.57          | ((X0) = (X1))
% 0.39/0.57          | ~ (v3_ordinal1 @ X1)
% 0.39/0.57          | ~ (r2_hidden @ X0 @ X1)
% 0.39/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 0.39/0.57          | ~ (v3_ordinal1 @ X0)
% 0.39/0.57          | (r2_xboole_0 @ X1 @ X0)
% 0.39/0.57          | ((X0) = (X1))
% 0.39/0.57          | ~ (v3_ordinal1 @ X1)
% 0.39/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.39/0.57          | ~ (r2_hidden @ X0 @ X1)
% 0.39/0.57          | ~ (v3_ordinal1 @ X1)
% 0.39/0.57          | ((X0) = (X1))
% 0.39/0.57          | (r2_hidden @ X1 @ X0)
% 0.39/0.57          | ~ (v3_ordinal1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['28', '37'])).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((r2_hidden @ X1 @ X0)
% 0.39/0.57          | ~ (r2_hidden @ X0 @ X1)
% 0.39/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.39/0.57          | ~ (v3_ordinal1 @ X1)
% 0.39/0.57          | ((X0) = (X1))
% 0.39/0.57          | (r2_xboole_0 @ X1 @ X0)
% 0.39/0.57          | ~ (v3_ordinal1 @ X0)
% 0.39/0.57          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['38'])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      ((~ (v3_ordinal1 @ sk_B)
% 0.39/0.57        | (r2_xboole_0 @ sk_A @ sk_B)
% 0.39/0.57        | ((sk_B) = (sk_A))
% 0.39/0.57        | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.39/0.57        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.39/0.57        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['27', '39'])).
% 0.39/0.57  thf('41', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('42', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      (((r2_xboole_0 @ sk_A @ sk_B)
% 0.39/0.57        | ((sk_B) = (sk_A))
% 0.39/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.39/0.57        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.39/0.57        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.39/0.57  thf('44', plain, (((sk_A) != (sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('45', plain,
% 0.39/0.57      (((r2_xboole_0 @ sk_A @ sk_B)
% 0.39/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.39/0.57        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.39/0.57        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      ((~ (v3_ordinal1 @ sk_A)
% 0.39/0.57        | (r2_hidden @ sk_A @ sk_B)
% 0.39/0.57        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.39/0.57        | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['26', '45'])).
% 0.39/0.57  thf('47', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('48', plain,
% 0.39/0.57      (((r2_hidden @ sk_A @ sk_B)
% 0.39/0.57        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.39/0.57        | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.39/0.57  thf('49', plain,
% 0.39/0.57      ((~ (v3_ordinal1 @ sk_B)
% 0.39/0.57        | (r2_hidden @ sk_A @ sk_B)
% 0.39/0.57        | ((sk_B) = (sk_A))
% 0.39/0.57        | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.57        | (r2_xboole_0 @ sk_A @ sk_B)
% 0.39/0.57        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['25', '48'])).
% 0.39/0.57  thf('50', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('51', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('52', plain,
% 0.39/0.57      (((r2_hidden @ sk_A @ sk_B)
% 0.39/0.57        | ((sk_B) = (sk_A))
% 0.39/0.57        | (r2_xboole_0 @ sk_A @ sk_B)
% 0.39/0.57        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.39/0.57  thf('53', plain,
% 0.39/0.57      (((r2_xboole_0 @ sk_A @ sk_B)
% 0.39/0.57        | ((sk_B) = (sk_A))
% 0.39/0.57        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.57      inference('simplify', [status(thm)], ['52'])).
% 0.39/0.57  thf('54', plain, (((sk_A) != (sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('55', plain, (((r2_xboole_0 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.39/0.57  thf('56', plain,
% 0.39/0.57      (![X23 : $i, X24 : $i]:
% 0.39/0.57         (~ (v3_ordinal1 @ X23)
% 0.39/0.57          | ((X24) = (k1_wellord1 @ (k1_wellord2 @ X23) @ X24))
% 0.39/0.57          | ~ (r2_hidden @ X24 @ X23)
% 0.39/0.57          | ~ (v3_ordinal1 @ X24))),
% 0.39/0.57      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.39/0.57  thf('57', plain,
% 0.39/0.57      (((r2_xboole_0 @ sk_A @ sk_B)
% 0.39/0.57        | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.57        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.39/0.57        | ~ (v3_ordinal1 @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['55', '56'])).
% 0.39/0.57  thf('58', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('59', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('60', plain,
% 0.39/0.57      (((r2_xboole_0 @ sk_A @ sk_B)
% 0.39/0.57        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.39/0.57  thf('61', plain,
% 0.39/0.57      (![X16 : $i, X17 : $i]:
% 0.39/0.57         (~ (v2_wellord1 @ X16)
% 0.39/0.57          | ~ (r4_wellord1 @ X16 @ 
% 0.39/0.57               (k2_wellord1 @ X16 @ (k1_wellord1 @ X16 @ X17)))
% 0.39/0.57          | ~ (r2_hidden @ X17 @ (k3_relat_1 @ X16))
% 0.39/0.57          | ~ (v1_relat_1 @ X16))),
% 0.39/0.57      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.39/0.57  thf('62', plain,
% 0.39/0.57      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ 
% 0.39/0.57           (k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.39/0.57        | (r2_xboole_0 @ sk_A @ sk_B)
% 0.39/0.57        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B))
% 0.39/0.57        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ (k1_wellord2 @ sk_B)))
% 0.39/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.39/0.57  thf('63', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.57  thf('64', plain, (![X18 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X18)) = (X18))),
% 0.39/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf('65', plain,
% 0.39/0.57      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ 
% 0.39/0.57           (k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.39/0.57        | (r2_xboole_0 @ sk_A @ sk_B)
% 0.39/0.57        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.39/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 0.39/0.57      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.39/0.57  thf('66', plain,
% 0.39/0.57      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_B))
% 0.39/0.57        | ~ (v3_ordinal1 @ sk_B)
% 0.39/0.57        | (r2_xboole_0 @ sk_A @ sk_B)
% 0.39/0.57        | ((sk_B) = (sk_A))
% 0.39/0.57        | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.39/0.57        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.39/0.57        | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['24', '65'])).
% 0.39/0.57  thf('67', plain,
% 0.39/0.57      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('68', plain,
% 0.39/0.57      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t50_wellord1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( v1_relat_1 @ B ) =>
% 0.39/0.57           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.39/0.57  thf('69', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X11)
% 0.39/0.57          | (r4_wellord1 @ X11 @ X12)
% 0.39/0.57          | ~ (r4_wellord1 @ X12 @ X11)
% 0.39/0.57          | ~ (v1_relat_1 @ X12))),
% 0.39/0.57      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.39/0.57  thf('70', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.39/0.57        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.39/0.57        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['68', '69'])).
% 0.39/0.57  thf('71', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.57  thf('72', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.57  thf('73', plain,
% 0.39/0.57      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.39/0.57  thf(t52_wellord1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( v1_relat_1 @ B ) =>
% 0.39/0.57           ( ![C:$i]:
% 0.39/0.57             ( ( v1_relat_1 @ C ) =>
% 0.39/0.57               ( ( ( r4_wellord1 @ A @ B ) & ( r4_wellord1 @ B @ C ) ) =>
% 0.39/0.57                 ( r4_wellord1 @ A @ C ) ) ) ) ) ) ))).
% 0.39/0.57  thf('74', plain,
% 0.39/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X13)
% 0.39/0.57          | ~ (r4_wellord1 @ X14 @ X13)
% 0.39/0.57          | ~ (r4_wellord1 @ X13 @ X15)
% 0.39/0.57          | (r4_wellord1 @ X14 @ X15)
% 0.39/0.57          | ~ (v1_relat_1 @ X15)
% 0.39/0.57          | ~ (v1_relat_1 @ X14))),
% 0.39/0.57      inference('cnf', [status(esa)], [t52_wellord1])).
% 0.39/0.57  thf('75', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ (k1_wellord2 @ sk_B))
% 0.39/0.57          | ~ (v1_relat_1 @ X0)
% 0.39/0.57          | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ X0)
% 0.39/0.57          | ~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ X0)
% 0.39/0.57          | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['73', '74'])).
% 0.39/0.57  thf('76', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.57  thf('77', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.57  thf('78', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X0)
% 0.39/0.57          | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ X0)
% 0.39/0.57          | ~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.39/0.57  thf('79', plain,
% 0.39/0.57      (((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_B))
% 0.39/0.57        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['67', '78'])).
% 0.39/0.57  thf('80', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.57  thf('81', plain,
% 0.39/0.57      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['79', '80'])).
% 0.39/0.57  thf('82', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('83', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('84', plain,
% 0.39/0.57      (((r2_xboole_0 @ sk_A @ sk_B)
% 0.39/0.57        | ((sk_B) = (sk_A))
% 0.39/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.39/0.57        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.39/0.57        | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['66', '81', '82', '83'])).
% 0.39/0.57  thf('85', plain,
% 0.39/0.57      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.39/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.39/0.57        | ((sk_B) = (sk_A))
% 0.39/0.57        | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('simplify', [status(thm)], ['84'])).
% 0.39/0.57  thf('86', plain, (((sk_A) != (sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('87', plain,
% 0.39/0.57      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.39/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.39/0.57        | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 0.39/0.57  thf('88', plain, (((r2_xboole_0 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.39/0.57  thf('89', plain,
% 0.39/0.57      (((r2_xboole_0 @ sk_A @ sk_B) | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 0.39/0.57      inference('clc', [status(thm)], ['87', '88'])).
% 0.39/0.57  thf('90', plain, ((~ (v3_ordinal1 @ sk_B) | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['3', '89'])).
% 0.39/0.57  thf('91', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('92', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.39/0.57      inference('demod', [status(thm)], ['90', '91'])).
% 0.39/0.57  thf('93', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.39/0.57  thf('94', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.39/0.57      inference('sup-', [status(thm)], ['92', '93'])).
% 0.39/0.57  thf('95', plain,
% 0.39/0.57      (![X26 : $i, X27 : $i]:
% 0.39/0.57         (((k2_wellord1 @ (k1_wellord2 @ X27) @ X26) = (k1_wellord2 @ X26))
% 0.39/0.57          | ~ (r1_tarski @ X26 @ X27))),
% 0.39/0.57      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.39/0.58  thf('96', plain,
% 0.39/0.58      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['94', '95'])).
% 0.39/0.58  thf('97', plain,
% 0.39/0.58      (![X10 : $i]:
% 0.39/0.58         (((k2_wellord1 @ X10 @ (k3_relat_1 @ X10)) = (X10))
% 0.39/0.58          | ~ (v1_relat_1 @ X10))),
% 0.39/0.58      inference('cnf', [status(esa)], [t30_wellord1])).
% 0.39/0.58  thf('98', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.58         (((k2_wellord1 @ (k2_wellord1 @ X7 @ X9) @ X8)
% 0.39/0.58            = (k2_wellord1 @ (k2_wellord1 @ X7 @ X8) @ X9))
% 0.39/0.58          | ~ (v1_relat_1 @ X7))),
% 0.39/0.58      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.39/0.58  thf('99', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (((k2_wellord1 @ X0 @ X1)
% 0.39/0.58            = (k2_wellord1 @ (k2_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0)))
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['97', '98'])).
% 0.39/0.58  thf('100', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | ((k2_wellord1 @ X0 @ X1)
% 0.39/0.58              = (k2_wellord1 @ (k2_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0))))),
% 0.39/0.58      inference('simplify', [status(thm)], ['99'])).
% 0.39/0.58  thf('101', plain,
% 0.39/0.58      ((((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A)
% 0.39/0.58          = (k2_wellord1 @ (k1_wellord2 @ sk_A) @ 
% 0.39/0.58             (k3_relat_1 @ (k1_wellord2 @ sk_B))))
% 0.39/0.58        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['96', '100'])).
% 0.39/0.58  thf('102', plain,
% 0.39/0.58      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['94', '95'])).
% 0.39/0.58  thf('103', plain,
% 0.39/0.58      (![X18 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X18)) = (X18))),
% 0.39/0.58      inference('demod', [status(thm)], ['11', '12'])).
% 0.39/0.58  thf('104', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.58  thf('105', plain,
% 0.39/0.58      (((k1_wellord2 @ sk_A) = (k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['101', '102', '103', '104'])).
% 0.39/0.58  thf('106', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.39/0.58             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.39/0.58          | ~ (v3_ordinal1 @ X0)
% 0.39/0.58          | (r2_hidden @ X1 @ X0)
% 0.39/0.58          | ((X0) = (X1))
% 0.39/0.58          | ~ (v3_ordinal1 @ X1)
% 0.39/0.58          | ~ (r2_hidden @ X0 @ X1)
% 0.39/0.58          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.39/0.58      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.39/0.58  thf('107', plain,
% 0.39/0.58      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_A))
% 0.39/0.58        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.39/0.58        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.39/0.58        | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.58        | ((sk_B) = (sk_A))
% 0.39/0.58        | (r2_hidden @ sk_A @ sk_B)
% 0.39/0.58        | ~ (v3_ordinal1 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['105', '106'])).
% 0.39/0.58  thf('108', plain,
% 0.39/0.58      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.39/0.58  thf('109', plain,
% 0.39/0.58      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('110', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X13)
% 0.39/0.58          | ~ (r4_wellord1 @ X14 @ X13)
% 0.39/0.58          | ~ (r4_wellord1 @ X13 @ X15)
% 0.39/0.58          | (r4_wellord1 @ X14 @ X15)
% 0.39/0.58          | ~ (v1_relat_1 @ X15)
% 0.39/0.58          | ~ (v1_relat_1 @ X14))),
% 0.39/0.58      inference('cnf', [status(esa)], [t52_wellord1])).
% 0.39/0.58  thf('111', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | (r4_wellord1 @ (k1_wellord2 @ sk_A) @ X0)
% 0.39/0.58          | ~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['109', '110'])).
% 0.39/0.58  thf('112', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.58  thf('113', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.58  thf('114', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | (r4_wellord1 @ (k1_wellord2 @ sk_A) @ X0)
% 0.39/0.58          | ~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ X0))),
% 0.39/0.58      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.39/0.58  thf('115', plain,
% 0.39/0.58      (((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_A))
% 0.39/0.58        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['108', '114'])).
% 0.39/0.58  thf('116', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.58  thf('117', plain,
% 0.39/0.58      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['115', '116'])).
% 0.39/0.58  thf('118', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('119', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('120', plain,
% 0.39/0.58      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.39/0.58        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.39/0.58        | ((sk_B) = (sk_A))
% 0.39/0.58        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['107', '117', '118', '119'])).
% 0.39/0.58  thf('121', plain, (((sk_A) != (sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('122', plain,
% 0.39/0.58      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.39/0.58        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.39/0.58        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['120', '121'])).
% 0.39/0.58  thf('123', plain,
% 0.39/0.58      ((~ (v3_ordinal1 @ sk_A)
% 0.39/0.58        | (r2_hidden @ sk_A @ sk_B)
% 0.39/0.58        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['2', '122'])).
% 0.39/0.58  thf('124', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('125', plain,
% 0.39/0.58      (((r2_hidden @ sk_A @ sk_B) | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['123', '124'])).
% 0.39/0.58  thf('126', plain,
% 0.39/0.58      ((~ (v3_ordinal1 @ sk_B)
% 0.39/0.58        | (r2_hidden @ sk_A @ sk_B)
% 0.39/0.58        | ((sk_B) = (sk_A))
% 0.39/0.58        | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.58        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '125'])).
% 0.39/0.58  thf('127', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('128', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('129', plain,
% 0.39/0.58      (((r2_hidden @ sk_A @ sk_B)
% 0.39/0.58        | ((sk_B) = (sk_A))
% 0.39/0.58        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['126', '127', '128'])).
% 0.39/0.58  thf('130', plain, ((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.58      inference('simplify', [status(thm)], ['129'])).
% 0.39/0.58  thf('131', plain, (((sk_A) != (sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('132', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['130', '131'])).
% 0.39/0.58  thf('133', plain,
% 0.39/0.58      (![X23 : $i, X24 : $i]:
% 0.39/0.58         (~ (v3_ordinal1 @ X23)
% 0.39/0.58          | ((X24) = (k1_wellord1 @ (k1_wellord2 @ X23) @ X24))
% 0.39/0.58          | ~ (r2_hidden @ X24 @ X23)
% 0.39/0.58          | ~ (v3_ordinal1 @ X24))),
% 0.39/0.58      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.39/0.58  thf('134', plain,
% 0.39/0.58      ((~ (v3_ordinal1 @ sk_A)
% 0.39/0.58        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.39/0.58        | ~ (v3_ordinal1 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['132', '133'])).
% 0.39/0.58  thf('135', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('136', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('137', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.39/0.58  thf('138', plain,
% 0.39/0.58      (![X16 : $i, X17 : $i]:
% 0.39/0.58         (~ (v2_wellord1 @ X16)
% 0.39/0.58          | ~ (r4_wellord1 @ X16 @ 
% 0.39/0.58               (k2_wellord1 @ X16 @ (k1_wellord1 @ X16 @ X17)))
% 0.39/0.58          | ~ (r2_hidden @ X17 @ (k3_relat_1 @ X16))
% 0.39/0.58          | ~ (v1_relat_1 @ X16))),
% 0.39/0.58      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.39/0.58  thf('139', plain,
% 0.39/0.58      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ 
% 0.39/0.58           (k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.39/0.58        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B))
% 0.39/0.58        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ (k1_wellord2 @ sk_B)))
% 0.39/0.58        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['137', '138'])).
% 0.39/0.58  thf('140', plain,
% 0.39/0.58      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['94', '95'])).
% 0.39/0.58  thf('141', plain,
% 0.39/0.58      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.39/0.58  thf('142', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.58  thf('143', plain,
% 0.39/0.58      (![X18 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X18)) = (X18))),
% 0.39/0.58      inference('demod', [status(thm)], ['11', '12'])).
% 0.39/0.58  thf('144', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['130', '131'])).
% 0.39/0.58  thf('145', plain, (~ (v2_wellord1 @ (k1_wellord2 @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)],
% 0.39/0.58                ['139', '140', '141', '142', '143', '144'])).
% 0.39/0.58  thf('146', plain, (~ (v3_ordinal1 @ sk_B)),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '145'])).
% 0.39/0.58  thf('147', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('148', plain, ($false), inference('demod', [status(thm)], ['146', '147'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
