%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.icR0Eo2JN5

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:53 EST 2020

% Result     : Theorem 2.27s
% Output     : Refutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 487 expanded)
%              Number of leaves         :   40 ( 165 expanded)
%              Depth                    :   25
%              Number of atoms          : 1138 (3742 expanded)
%              Number of equality atoms :   62 ( 205 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X50: $i] :
      ( ( ( k3_relat_1 @ X50 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X50: $i] :
      ( ( ( k3_relat_1 @ X50 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( k2_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( r1_tarski @ ( k2_xboole_0 @ X24 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ X52 ) @ ( k1_relat_1 @ X51 ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ X52 @ X51 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t15_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X52 ) @ ( k1_relat_1 @ X51 ) ) @ ( k1_relat_1 @ ( k4_xboole_0 @ X52 @ X51 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('26',plain,(
    ! [X45: $i,X48: $i] :
      ( ( X48
        = ( k1_relat_1 @ X45 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X48 @ X45 ) @ ( sk_D_2 @ X48 @ X45 ) ) @ X45 )
      | ( r2_hidden @ ( sk_C_2 @ X48 @ X45 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('27',plain,(
    ! [X21: $i] :
      ( r1_xboole_0 @ X21 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('28',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X28 != X27 )
      | ( r2_hidden @ X28 @ X29 )
      | ( X29
       != ( k2_tarski @ X30 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('29',plain,(
    ! [X27: $i,X30: $i] :
      ( r2_hidden @ X27 @ ( k2_tarski @ X30 @ X27 ) ) ),
    inference(simplify,[status(thm)],['28'])).

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

thf('30',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('35',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['25','35'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('37',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('38',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( k2_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','45'])).

thf('47',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['2','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('51',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( r1_tarski @ ( k2_xboole_0 @ X24 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('55',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('59',plain,(
    ! [X50: $i] :
      ( ( ( k3_relat_1 @ X50 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('61',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( k2_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_xboole_0 @ ( k3_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','63'])).

thf('65',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['57','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('69',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_B_1 ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('71',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_B_1 ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t28_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('73',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( v1_relat_1 @ X55 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ X56 ) @ ( k2_relat_1 @ X55 ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ X56 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t28_relat_1])).

thf('74',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('75',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('76',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( v1_relat_1 @ X55 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X56 ) @ ( k2_relat_1 @ X55 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X56 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['72','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) @ ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('81',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('82',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('83',plain,(
    ! [X50: $i] :
      ( ( ( k3_relat_1 @ X50 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('84',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('86',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('87',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( r1_tarski @ ( k2_xboole_0 @ X24 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('91',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','93'])).

thf('95',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','94'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('96',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('97',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) @ ( k3_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','97'])).

thf('99',plain,(
    ! [X27: $i,X30: $i] :
      ( r2_hidden @ X27 @ ( k2_tarski @ X30 @ X27 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('100',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('101',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('102',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) )).

thf('103',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X53 ) @ ( k1_relat_1 @ X53 ) )
      | ~ ( r2_hidden @ X54 @ ( k2_relat_1 @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_3 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C_3 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ ( sk_C_3 @ k1_xboole_0 ) @ X0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('109',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('110',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_3 @ k1_xboole_0 ) @ X0 )
      | ( ( k3_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['107','110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k3_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_3 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','112'])).

thf('114',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_3 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','115'])).

thf('117',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['98','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('119',plain,
    ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('121',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( k2_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['71','124'])).

thf('126',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('127',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( r1_tarski @ ( k2_xboole_0 @ X24 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B_1 ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['125','128'])).

thf('130',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    $false ),
    inference(demod,[status(thm)],['0','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.icR0Eo2JN5
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:10:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.27/2.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.27/2.49  % Solved by: fo/fo7.sh
% 2.27/2.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.27/2.49  % done 3635 iterations in 2.045s
% 2.27/2.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.27/2.49  % SZS output start Refutation
% 2.27/2.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.27/2.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.27/2.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.27/2.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.27/2.49  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 2.27/2.49  thf(sk_B_type, type, sk_B: $i > $i).
% 2.27/2.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.27/2.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.27/2.49  thf(sk_A_type, type, sk_A: $i).
% 2.27/2.49  thf(sk_C_3_type, type, sk_C_3: $i > $i).
% 2.27/2.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.27/2.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.27/2.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 2.27/2.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.27/2.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.27/2.49  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 2.27/2.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.27/2.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.27/2.49  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 2.27/2.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.27/2.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.27/2.49  thf(t31_relat_1, conjecture,
% 2.27/2.49    (![A:$i]:
% 2.27/2.49     ( ( v1_relat_1 @ A ) =>
% 2.27/2.49       ( ![B:$i]:
% 2.27/2.49         ( ( v1_relat_1 @ B ) =>
% 2.27/2.49           ( ( r1_tarski @ A @ B ) =>
% 2.27/2.49             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 2.27/2.49  thf(zf_stmt_0, negated_conjecture,
% 2.27/2.49    (~( ![A:$i]:
% 2.27/2.49        ( ( v1_relat_1 @ A ) =>
% 2.27/2.49          ( ![B:$i]:
% 2.27/2.49            ( ( v1_relat_1 @ B ) =>
% 2.27/2.49              ( ( r1_tarski @ A @ B ) =>
% 2.27/2.49                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 2.27/2.49    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 2.27/2.49  thf('0', plain,
% 2.27/2.49      (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 2.27/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.49  thf(d6_relat_1, axiom,
% 2.27/2.49    (![A:$i]:
% 2.27/2.49     ( ( v1_relat_1 @ A ) =>
% 2.27/2.49       ( ( k3_relat_1 @ A ) =
% 2.27/2.49         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 2.27/2.49  thf('1', plain,
% 2.27/2.49      (![X50 : $i]:
% 2.27/2.49         (((k3_relat_1 @ X50)
% 2.27/2.49            = (k2_xboole_0 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50)))
% 2.27/2.49          | ~ (v1_relat_1 @ X50))),
% 2.27/2.49      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.27/2.49  thf('2', plain,
% 2.27/2.49      (![X50 : $i]:
% 2.27/2.49         (((k3_relat_1 @ X50)
% 2.27/2.49            = (k2_xboole_0 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50)))
% 2.27/2.49          | ~ (v1_relat_1 @ X50))),
% 2.27/2.49      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.27/2.49  thf(t7_xboole_1, axiom,
% 2.27/2.49    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.27/2.49  thf('3', plain,
% 2.27/2.49      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 2.27/2.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.27/2.49  thf(d10_xboole_0, axiom,
% 2.27/2.49    (![A:$i,B:$i]:
% 2.27/2.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.27/2.49  thf('4', plain,
% 2.27/2.49      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 2.27/2.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.27/2.49  thf('5', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 2.27/2.49      inference('simplify', [status(thm)], ['4'])).
% 2.27/2.49  thf(t10_xboole_1, axiom,
% 2.27/2.49    (![A:$i,B:$i,C:$i]:
% 2.27/2.49     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 2.27/2.49  thf('6', plain,
% 2.27/2.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.27/2.49         (~ (r1_tarski @ X11 @ X12)
% 2.27/2.49          | (r1_tarski @ X11 @ (k2_xboole_0 @ X13 @ X12)))),
% 2.27/2.49      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.27/2.49  thf('7', plain,
% 2.27/2.49      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.27/2.49      inference('sup-', [status(thm)], ['5', '6'])).
% 2.27/2.49  thf(t8_xboole_1, axiom,
% 2.27/2.49    (![A:$i,B:$i,C:$i]:
% 2.27/2.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.27/2.49       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.27/2.49  thf('8', plain,
% 2.27/2.49      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.27/2.49         (~ (r1_tarski @ X24 @ X25)
% 2.27/2.49          | ~ (r1_tarski @ X26 @ X25)
% 2.27/2.49          | (r1_tarski @ (k2_xboole_0 @ X24 @ X26) @ X25))),
% 2.27/2.49      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.27/2.49  thf('9', plain,
% 2.27/2.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.27/2.49         ((r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 2.27/2.49          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.27/2.49      inference('sup-', [status(thm)], ['7', '8'])).
% 2.27/2.49  thf('10', plain,
% 2.27/2.49      (![X0 : $i, X1 : $i]:
% 2.27/2.49         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 2.27/2.49      inference('sup-', [status(thm)], ['3', '9'])).
% 2.27/2.49  thf('11', plain,
% 2.27/2.49      (![X5 : $i, X7 : $i]:
% 2.27/2.49         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 2.27/2.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.27/2.49  thf('12', plain,
% 2.27/2.49      (![X0 : $i, X1 : $i]:
% 2.27/2.49         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 2.27/2.49          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1)))),
% 2.27/2.49      inference('sup-', [status(thm)], ['10', '11'])).
% 2.27/2.49  thf('13', plain,
% 2.27/2.49      (![X0 : $i, X1 : $i]:
% 2.27/2.49         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 2.27/2.49      inference('sup-', [status(thm)], ['3', '9'])).
% 2.27/2.49  thf('14', plain,
% 2.27/2.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.27/2.49      inference('demod', [status(thm)], ['12', '13'])).
% 2.27/2.49  thf('15', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 2.27/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.49  thf(l32_xboole_1, axiom,
% 2.27/2.49    (![A:$i,B:$i]:
% 2.27/2.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.27/2.49  thf('16', plain,
% 2.27/2.49      (![X8 : $i, X10 : $i]:
% 2.27/2.49         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 2.27/2.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.27/2.49  thf('17', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 2.27/2.49      inference('sup-', [status(thm)], ['15', '16'])).
% 2.27/2.49  thf(t15_relat_1, axiom,
% 2.27/2.49    (![A:$i]:
% 2.27/2.49     ( ( v1_relat_1 @ A ) =>
% 2.27/2.49       ( ![B:$i]:
% 2.27/2.49         ( ( v1_relat_1 @ B ) =>
% 2.27/2.49           ( r1_tarski @
% 2.27/2.49             ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ 
% 2.27/2.49             ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 2.27/2.49  thf('18', plain,
% 2.27/2.49      (![X51 : $i, X52 : $i]:
% 2.27/2.49         (~ (v1_relat_1 @ X51)
% 2.27/2.49          | (r1_tarski @ 
% 2.27/2.49             (k6_subset_1 @ (k1_relat_1 @ X52) @ (k1_relat_1 @ X51)) @ 
% 2.27/2.49             (k1_relat_1 @ (k6_subset_1 @ X52 @ X51)))
% 2.27/2.49          | ~ (v1_relat_1 @ X52))),
% 2.27/2.49      inference('cnf', [status(esa)], [t15_relat_1])).
% 2.27/2.49  thf(redefinition_k6_subset_1, axiom,
% 2.27/2.49    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.27/2.49  thf('19', plain,
% 2.27/2.49      (![X40 : $i, X41 : $i]:
% 2.27/2.49         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 2.27/2.49      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.27/2.49  thf('20', plain,
% 2.27/2.49      (![X40 : $i, X41 : $i]:
% 2.27/2.49         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 2.27/2.49      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.27/2.49  thf('21', plain,
% 2.27/2.49      (![X51 : $i, X52 : $i]:
% 2.27/2.49         (~ (v1_relat_1 @ X51)
% 2.27/2.49          | (r1_tarski @ 
% 2.27/2.49             (k4_xboole_0 @ (k1_relat_1 @ X52) @ (k1_relat_1 @ X51)) @ 
% 2.27/2.49             (k1_relat_1 @ (k4_xboole_0 @ X52 @ X51)))
% 2.27/2.49          | ~ (v1_relat_1 @ X52))),
% 2.27/2.49      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.27/2.49  thf('22', plain,
% 2.27/2.49      (((r1_tarski @ 
% 2.27/2.49         (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)) @ 
% 2.27/2.49         (k1_relat_1 @ k1_xboole_0))
% 2.27/2.49        | ~ (v1_relat_1 @ sk_A)
% 2.27/2.49        | ~ (v1_relat_1 @ sk_B_1))),
% 2.27/2.49      inference('sup+', [status(thm)], ['17', '21'])).
% 2.27/2.49  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 2.27/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.49  thf('24', plain, ((v1_relat_1 @ sk_B_1)),
% 2.27/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.49  thf('25', plain,
% 2.27/2.49      ((r1_tarski @ 
% 2.27/2.49        (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)) @ 
% 2.27/2.49        (k1_relat_1 @ k1_xboole_0))),
% 2.27/2.49      inference('demod', [status(thm)], ['22', '23', '24'])).
% 2.27/2.49  thf(d4_relat_1, axiom,
% 2.27/2.49    (![A:$i,B:$i]:
% 2.27/2.49     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 2.27/2.49       ( ![C:$i]:
% 2.27/2.49         ( ( r2_hidden @ C @ B ) <=>
% 2.27/2.49           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 2.27/2.49  thf('26', plain,
% 2.27/2.49      (![X45 : $i, X48 : $i]:
% 2.27/2.49         (((X48) = (k1_relat_1 @ X45))
% 2.27/2.49          | (r2_hidden @ 
% 2.27/2.49             (k4_tarski @ (sk_C_2 @ X48 @ X45) @ (sk_D_2 @ X48 @ X45)) @ X45)
% 2.27/2.49          | (r2_hidden @ (sk_C_2 @ X48 @ X45) @ X48))),
% 2.27/2.49      inference('cnf', [status(esa)], [d4_relat_1])).
% 2.27/2.49  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 2.27/2.50  thf('27', plain, (![X21 : $i]: (r1_xboole_0 @ X21 @ k1_xboole_0)),
% 2.27/2.50      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.27/2.50  thf(d2_tarski, axiom,
% 2.27/2.50    (![A:$i,B:$i,C:$i]:
% 2.27/2.50     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 2.27/2.50       ( ![D:$i]:
% 2.27/2.50         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 2.27/2.50  thf('28', plain,
% 2.27/2.50      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 2.27/2.50         (((X28) != (X27))
% 2.27/2.50          | (r2_hidden @ X28 @ X29)
% 2.27/2.50          | ((X29) != (k2_tarski @ X30 @ X27)))),
% 2.27/2.50      inference('cnf', [status(esa)], [d2_tarski])).
% 2.27/2.50  thf('29', plain,
% 2.27/2.50      (![X27 : $i, X30 : $i]: (r2_hidden @ X27 @ (k2_tarski @ X30 @ X27))),
% 2.27/2.50      inference('simplify', [status(thm)], ['28'])).
% 2.27/2.50  thf(t3_xboole_0, axiom,
% 2.27/2.50    (![A:$i,B:$i]:
% 2.27/2.50     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.27/2.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.27/2.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.27/2.50            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.27/2.50  thf('30', plain,
% 2.27/2.50      (![X0 : $i, X2 : $i, X3 : $i]:
% 2.27/2.50         (~ (r2_hidden @ X2 @ X0)
% 2.27/2.50          | ~ (r2_hidden @ X2 @ X3)
% 2.27/2.50          | ~ (r1_xboole_0 @ X0 @ X3))),
% 2.27/2.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.27/2.50  thf('31', plain,
% 2.27/2.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.27/2.50         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 2.27/2.50          | ~ (r2_hidden @ X0 @ X2))),
% 2.27/2.50      inference('sup-', [status(thm)], ['29', '30'])).
% 2.27/2.50  thf('32', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.27/2.50      inference('sup-', [status(thm)], ['27', '31'])).
% 2.27/2.50  thf('33', plain,
% 2.27/2.50      (![X0 : $i]:
% 2.27/2.50         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 2.27/2.50          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 2.27/2.50      inference('sup-', [status(thm)], ['26', '32'])).
% 2.27/2.50  thf('34', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.27/2.50      inference('sup-', [status(thm)], ['27', '31'])).
% 2.27/2.50  thf('35', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.27/2.50      inference('sup-', [status(thm)], ['33', '34'])).
% 2.27/2.50  thf('36', plain,
% 2.27/2.50      ((r1_tarski @ 
% 2.27/2.50        (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)) @ 
% 2.27/2.50        k1_xboole_0)),
% 2.27/2.50      inference('demod', [status(thm)], ['25', '35'])).
% 2.27/2.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.27/2.50  thf('37', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 2.27/2.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.27/2.50  thf('38', plain,
% 2.27/2.50      (![X5 : $i, X7 : $i]:
% 2.27/2.50         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 2.27/2.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.27/2.50  thf('39', plain,
% 2.27/2.50      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.27/2.50      inference('sup-', [status(thm)], ['37', '38'])).
% 2.27/2.50  thf('40', plain,
% 2.27/2.50      (((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1))
% 2.27/2.50         = (k1_xboole_0))),
% 2.27/2.50      inference('sup-', [status(thm)], ['36', '39'])).
% 2.27/2.50  thf('41', plain,
% 2.27/2.50      (![X8 : $i, X9 : $i]:
% 2.27/2.50         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 2.27/2.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.27/2.50  thf('42', plain,
% 2.27/2.50      ((((k1_xboole_0) != (k1_xboole_0))
% 2.27/2.50        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))),
% 2.27/2.50      inference('sup-', [status(thm)], ['40', '41'])).
% 2.27/2.50  thf('43', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1))),
% 2.27/2.50      inference('simplify', [status(thm)], ['42'])).
% 2.27/2.50  thf('44', plain,
% 2.27/2.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.27/2.50         (~ (r1_tarski @ X11 @ X12)
% 2.27/2.50          | (r1_tarski @ X11 @ (k2_xboole_0 @ X13 @ X12)))),
% 2.27/2.50      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.27/2.50  thf('45', plain,
% 2.27/2.50      (![X0 : $i]:
% 2.27/2.50         (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 2.27/2.50          (k2_xboole_0 @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 2.27/2.50      inference('sup-', [status(thm)], ['43', '44'])).
% 2.27/2.50  thf('46', plain,
% 2.27/2.50      (![X0 : $i]:
% 2.27/2.50         (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 2.27/2.50          (k2_xboole_0 @ (k1_relat_1 @ sk_B_1) @ X0))),
% 2.27/2.50      inference('sup+', [status(thm)], ['14', '45'])).
% 2.27/2.50  thf('47', plain,
% 2.27/2.50      (((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))
% 2.27/2.50        | ~ (v1_relat_1 @ sk_B_1))),
% 2.27/2.50      inference('sup+', [status(thm)], ['2', '46'])).
% 2.27/2.50  thf('48', plain, ((v1_relat_1 @ sk_B_1)),
% 2.27/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.50  thf('49', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 2.27/2.50      inference('demod', [status(thm)], ['47', '48'])).
% 2.27/2.50  thf('50', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 2.27/2.50      inference('simplify', [status(thm)], ['4'])).
% 2.27/2.50  thf('51', plain,
% 2.27/2.50      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.27/2.50         (~ (r1_tarski @ X24 @ X25)
% 2.27/2.50          | ~ (r1_tarski @ X26 @ X25)
% 2.27/2.50          | (r1_tarski @ (k2_xboole_0 @ X24 @ X26) @ X25))),
% 2.27/2.50      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.27/2.50  thf('52', plain,
% 2.27/2.50      (![X0 : $i, X1 : $i]:
% 2.27/2.50         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 2.27/2.50      inference('sup-', [status(thm)], ['50', '51'])).
% 2.27/2.50  thf('53', plain,
% 2.27/2.50      ((r1_tarski @ 
% 2.27/2.50        (k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)) @ 
% 2.27/2.50        (k3_relat_1 @ sk_B_1))),
% 2.27/2.50      inference('sup-', [status(thm)], ['49', '52'])).
% 2.27/2.50  thf('54', plain,
% 2.27/2.50      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 2.27/2.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.27/2.50  thf('55', plain,
% 2.27/2.50      (![X5 : $i, X7 : $i]:
% 2.27/2.50         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 2.27/2.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.27/2.50  thf('56', plain,
% 2.27/2.50      (![X0 : $i, X1 : $i]:
% 2.27/2.50         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 2.27/2.50          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 2.27/2.50      inference('sup-', [status(thm)], ['54', '55'])).
% 2.27/2.50  thf('57', plain,
% 2.27/2.50      (((k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))
% 2.27/2.50         = (k3_relat_1 @ sk_B_1))),
% 2.27/2.50      inference('sup-', [status(thm)], ['53', '56'])).
% 2.27/2.50  thf('58', plain,
% 2.27/2.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.27/2.50      inference('demod', [status(thm)], ['12', '13'])).
% 2.27/2.50  thf('59', plain,
% 2.27/2.50      (![X50 : $i]:
% 2.27/2.50         (((k3_relat_1 @ X50)
% 2.27/2.50            = (k2_xboole_0 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50)))
% 2.27/2.50          | ~ (v1_relat_1 @ X50))),
% 2.27/2.50      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.27/2.50  thf('60', plain,
% 2.27/2.50      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.27/2.50      inference('sup-', [status(thm)], ['5', '6'])).
% 2.27/2.50  thf('61', plain,
% 2.27/2.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.27/2.50         (~ (r1_tarski @ X11 @ X12)
% 2.27/2.50          | (r1_tarski @ X11 @ (k2_xboole_0 @ X13 @ X12)))),
% 2.27/2.50      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.27/2.50  thf('62', plain,
% 2.27/2.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.27/2.50         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.27/2.50      inference('sup-', [status(thm)], ['60', '61'])).
% 2.27/2.50  thf('63', plain,
% 2.27/2.50      (![X0 : $i, X1 : $i]:
% 2.27/2.50         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 2.27/2.50           (k2_xboole_0 @ X1 @ (k3_relat_1 @ X0)))
% 2.27/2.50          | ~ (v1_relat_1 @ X0))),
% 2.27/2.50      inference('sup+', [status(thm)], ['59', '62'])).
% 2.27/2.50  thf('64', plain,
% 2.27/2.50      (![X0 : $i, X1 : $i]:
% 2.27/2.50         ((r1_tarski @ (k2_relat_1 @ X1) @ 
% 2.27/2.50           (k2_xboole_0 @ (k3_relat_1 @ X1) @ X0))
% 2.27/2.50          | ~ (v1_relat_1 @ X1))),
% 2.27/2.50      inference('sup+', [status(thm)], ['58', '63'])).
% 2.27/2.50  thf('65', plain,
% 2.27/2.50      (((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))
% 2.27/2.50        | ~ (v1_relat_1 @ sk_B_1))),
% 2.27/2.50      inference('sup+', [status(thm)], ['57', '64'])).
% 2.27/2.50  thf('66', plain, ((v1_relat_1 @ sk_B_1)),
% 2.27/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.50  thf('67', plain,
% 2.27/2.50      ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))),
% 2.27/2.50      inference('demod', [status(thm)], ['65', '66'])).
% 2.27/2.50  thf('68', plain,
% 2.27/2.50      (![X0 : $i, X1 : $i]:
% 2.27/2.50         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 2.27/2.50      inference('sup-', [status(thm)], ['50', '51'])).
% 2.27/2.50  thf('69', plain,
% 2.27/2.50      ((r1_tarski @ 
% 2.27/2.50        (k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_B_1)) @ 
% 2.27/2.50        (k3_relat_1 @ sk_B_1))),
% 2.27/2.50      inference('sup-', [status(thm)], ['67', '68'])).
% 2.27/2.50  thf('70', plain,
% 2.27/2.50      (![X0 : $i, X1 : $i]:
% 2.27/2.50         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 2.27/2.50          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 2.27/2.50      inference('sup-', [status(thm)], ['54', '55'])).
% 2.27/2.50  thf('71', plain,
% 2.27/2.50      (((k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_B_1))
% 2.27/2.50         = (k3_relat_1 @ sk_B_1))),
% 2.27/2.50      inference('sup-', [status(thm)], ['69', '70'])).
% 2.27/2.50  thf('72', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 2.27/2.50      inference('sup-', [status(thm)], ['15', '16'])).
% 2.27/2.50  thf(t28_relat_1, axiom,
% 2.27/2.50    (![A:$i]:
% 2.27/2.50     ( ( v1_relat_1 @ A ) =>
% 2.27/2.50       ( ![B:$i]:
% 2.27/2.50         ( ( v1_relat_1 @ B ) =>
% 2.27/2.50           ( r1_tarski @
% 2.27/2.50             ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 2.27/2.50             ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 2.27/2.50  thf('73', plain,
% 2.27/2.50      (![X55 : $i, X56 : $i]:
% 2.27/2.50         (~ (v1_relat_1 @ X55)
% 2.27/2.50          | (r1_tarski @ 
% 2.27/2.50             (k6_subset_1 @ (k2_relat_1 @ X56) @ (k2_relat_1 @ X55)) @ 
% 2.27/2.50             (k2_relat_1 @ (k6_subset_1 @ X56 @ X55)))
% 2.27/2.50          | ~ (v1_relat_1 @ X56))),
% 2.27/2.50      inference('cnf', [status(esa)], [t28_relat_1])).
% 2.27/2.50  thf('74', plain,
% 2.27/2.50      (![X40 : $i, X41 : $i]:
% 2.27/2.50         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 2.27/2.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.27/2.50  thf('75', plain,
% 2.27/2.50      (![X40 : $i, X41 : $i]:
% 2.27/2.50         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 2.27/2.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.27/2.50  thf('76', plain,
% 2.27/2.50      (![X55 : $i, X56 : $i]:
% 2.27/2.50         (~ (v1_relat_1 @ X55)
% 2.27/2.50          | (r1_tarski @ 
% 2.27/2.50             (k4_xboole_0 @ (k2_relat_1 @ X56) @ (k2_relat_1 @ X55)) @ 
% 2.27/2.50             (k2_relat_1 @ (k4_xboole_0 @ X56 @ X55)))
% 2.27/2.50          | ~ (v1_relat_1 @ X56))),
% 2.27/2.50      inference('demod', [status(thm)], ['73', '74', '75'])).
% 2.27/2.50  thf('77', plain,
% 2.27/2.50      (((r1_tarski @ 
% 2.27/2.50         (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)) @ 
% 2.27/2.50         (k2_relat_1 @ k1_xboole_0))
% 2.27/2.50        | ~ (v1_relat_1 @ sk_A)
% 2.27/2.50        | ~ (v1_relat_1 @ sk_B_1))),
% 2.27/2.50      inference('sup+', [status(thm)], ['72', '76'])).
% 2.27/2.50  thf('78', plain, ((v1_relat_1 @ sk_A)),
% 2.27/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.50  thf('79', plain, ((v1_relat_1 @ sk_B_1)),
% 2.27/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.50  thf('80', plain,
% 2.27/2.50      ((r1_tarski @ 
% 2.27/2.50        (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)) @ 
% 2.27/2.50        (k2_relat_1 @ k1_xboole_0))),
% 2.27/2.50      inference('demod', [status(thm)], ['77', '78', '79'])).
% 2.27/2.50  thf(cc1_relat_1, axiom,
% 2.27/2.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 2.27/2.50  thf('81', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 2.27/2.50      inference('cnf', [status(esa)], [cc1_relat_1])).
% 2.27/2.50  thf('82', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.27/2.50      inference('sup-', [status(thm)], ['33', '34'])).
% 2.27/2.50  thf('83', plain,
% 2.27/2.50      (![X50 : $i]:
% 2.27/2.50         (((k3_relat_1 @ X50)
% 2.27/2.50            = (k2_xboole_0 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50)))
% 2.27/2.50          | ~ (v1_relat_1 @ X50))),
% 2.27/2.50      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.27/2.50  thf('84', plain,
% 2.27/2.50      ((((k3_relat_1 @ k1_xboole_0)
% 2.27/2.50          = (k2_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))
% 2.27/2.50        | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.27/2.50      inference('sup+', [status(thm)], ['82', '83'])).
% 2.27/2.50  thf('85', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 2.27/2.50      inference('simplify', [status(thm)], ['4'])).
% 2.27/2.50  thf('86', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 2.27/2.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.27/2.50  thf('87', plain,
% 2.27/2.50      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.27/2.50         (~ (r1_tarski @ X24 @ X25)
% 2.27/2.50          | ~ (r1_tarski @ X26 @ X25)
% 2.27/2.50          | (r1_tarski @ (k2_xboole_0 @ X24 @ X26) @ X25))),
% 2.27/2.50      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.27/2.50  thf('88', plain,
% 2.27/2.50      (![X0 : $i, X1 : $i]:
% 2.27/2.50         ((r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ X0)
% 2.27/2.50          | ~ (r1_tarski @ X1 @ X0))),
% 2.27/2.50      inference('sup-', [status(thm)], ['86', '87'])).
% 2.27/2.50  thf('89', plain,
% 2.27/2.50      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 2.27/2.50      inference('sup-', [status(thm)], ['85', '88'])).
% 2.27/2.50  thf('90', plain,
% 2.27/2.50      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.27/2.50      inference('sup-', [status(thm)], ['5', '6'])).
% 2.27/2.50  thf('91', plain,
% 2.27/2.50      (![X5 : $i, X7 : $i]:
% 2.27/2.50         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 2.27/2.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.27/2.50  thf('92', plain,
% 2.27/2.50      (![X0 : $i, X1 : $i]:
% 2.27/2.50         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 2.27/2.50          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 2.27/2.50      inference('sup-', [status(thm)], ['90', '91'])).
% 2.27/2.50  thf('93', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.27/2.50      inference('sup-', [status(thm)], ['89', '92'])).
% 2.27/2.50  thf('94', plain,
% 2.27/2.50      ((((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 2.27/2.50        | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.27/2.50      inference('demod', [status(thm)], ['84', '93'])).
% 2.27/2.50  thf('95', plain,
% 2.27/2.50      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.27/2.50        | ((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 2.27/2.50      inference('sup-', [status(thm)], ['81', '94'])).
% 2.27/2.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.27/2.50  thf('96', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.27/2.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.27/2.50  thf('97', plain, (((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 2.27/2.50      inference('demod', [status(thm)], ['95', '96'])).
% 2.27/2.50  thf('98', plain,
% 2.27/2.50      ((r1_tarski @ 
% 2.27/2.50        (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)) @ 
% 2.27/2.50        (k3_relat_1 @ k1_xboole_0))),
% 2.27/2.50      inference('demod', [status(thm)], ['80', '97'])).
% 2.27/2.50  thf('99', plain,
% 2.27/2.50      (![X27 : $i, X30 : $i]: (r2_hidden @ X27 @ (k2_tarski @ X30 @ X27))),
% 2.27/2.50      inference('simplify', [status(thm)], ['28'])).
% 2.27/2.50  thf('100', plain,
% 2.27/2.50      (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 2.27/2.50      inference('cnf', [status(esa)], [cc1_relat_1])).
% 2.27/2.50  thf('101', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.27/2.50      inference('sup-', [status(thm)], ['33', '34'])).
% 2.27/2.50  thf(t7_xboole_0, axiom,
% 2.27/2.50    (![A:$i]:
% 2.27/2.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.27/2.50          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.27/2.50  thf('102', plain,
% 2.27/2.50      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 2.27/2.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.27/2.50  thf(t19_relat_1, axiom,
% 2.27/2.50    (![A:$i,B:$i]:
% 2.27/2.50     ( ( v1_relat_1 @ B ) =>
% 2.27/2.50       ( ~( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) & 
% 2.27/2.50            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 2.27/2.50  thf('103', plain,
% 2.27/2.50      (![X53 : $i, X54 : $i]:
% 2.27/2.50         ((r2_hidden @ (sk_C_3 @ X53) @ (k1_relat_1 @ X53))
% 2.27/2.50          | ~ (r2_hidden @ X54 @ (k2_relat_1 @ X53))
% 2.27/2.50          | ~ (v1_relat_1 @ X53))),
% 2.27/2.50      inference('cnf', [status(esa)], [t19_relat_1])).
% 2.27/2.50  thf('104', plain,
% 2.27/2.50      (![X0 : $i]:
% 2.27/2.50         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 2.27/2.50          | ~ (v1_relat_1 @ X0)
% 2.27/2.50          | (r2_hidden @ (sk_C_3 @ X0) @ (k1_relat_1 @ X0)))),
% 2.27/2.50      inference('sup-', [status(thm)], ['102', '103'])).
% 2.27/2.50  thf('105', plain,
% 2.27/2.50      (![X0 : $i, X2 : $i, X3 : $i]:
% 2.27/2.50         (~ (r2_hidden @ X2 @ X0)
% 2.27/2.50          | ~ (r2_hidden @ X2 @ X3)
% 2.27/2.50          | ~ (r1_xboole_0 @ X0 @ X3))),
% 2.27/2.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.27/2.50  thf('106', plain,
% 2.27/2.50      (![X0 : $i, X1 : $i]:
% 2.27/2.50         (~ (v1_relat_1 @ X0)
% 2.27/2.50          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 2.27/2.50          | ~ (r1_xboole_0 @ (k1_relat_1 @ X0) @ X1)
% 2.27/2.50          | ~ (r2_hidden @ (sk_C_3 @ X0) @ X1))),
% 2.27/2.50      inference('sup-', [status(thm)], ['104', '105'])).
% 2.27/2.50  thf('107', plain,
% 2.27/2.50      (![X0 : $i]:
% 2.27/2.50         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 2.27/2.50          | ~ (r2_hidden @ (sk_C_3 @ k1_xboole_0) @ X0)
% 2.27/2.50          | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 2.27/2.50          | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.27/2.50      inference('sup-', [status(thm)], ['101', '106'])).
% 2.27/2.50  thf('108', plain,
% 2.27/2.50      (![X0 : $i, X1 : $i]:
% 2.27/2.50         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 2.27/2.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.27/2.50  thf('109', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.27/2.50      inference('sup-', [status(thm)], ['27', '31'])).
% 2.27/2.50  thf('110', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.27/2.50      inference('sup-', [status(thm)], ['108', '109'])).
% 2.27/2.50  thf('111', plain,
% 2.27/2.50      (((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 2.27/2.50      inference('demod', [status(thm)], ['95', '96'])).
% 2.27/2.50  thf('112', plain,
% 2.27/2.50      (![X0 : $i]:
% 2.27/2.50         (~ (r2_hidden @ (sk_C_3 @ k1_xboole_0) @ X0)
% 2.27/2.50          | ((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 2.27/2.50          | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.27/2.50      inference('demod', [status(thm)], ['107', '110', '111'])).
% 2.27/2.50  thf('113', plain,
% 2.27/2.50      (![X0 : $i]:
% 2.27/2.50         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.27/2.50          | ((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 2.27/2.50          | ~ (r2_hidden @ (sk_C_3 @ k1_xboole_0) @ X0))),
% 2.27/2.50      inference('sup-', [status(thm)], ['100', '112'])).
% 2.27/2.50  thf('114', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.27/2.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.27/2.50  thf('115', plain,
% 2.27/2.50      (![X0 : $i]:
% 2.27/2.50         (((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 2.27/2.50          | ~ (r2_hidden @ (sk_C_3 @ k1_xboole_0) @ X0))),
% 2.27/2.50      inference('demod', [status(thm)], ['113', '114'])).
% 2.27/2.50  thf('116', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.27/2.50      inference('sup-', [status(thm)], ['99', '115'])).
% 2.27/2.50  thf('117', plain,
% 2.27/2.50      ((r1_tarski @ 
% 2.27/2.50        (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)) @ 
% 2.27/2.50        k1_xboole_0)),
% 2.27/2.50      inference('demod', [status(thm)], ['98', '116'])).
% 2.27/2.50  thf('118', plain,
% 2.27/2.50      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.27/2.50      inference('sup-', [status(thm)], ['37', '38'])).
% 2.27/2.50  thf('119', plain,
% 2.27/2.50      (((k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 2.27/2.50         = (k1_xboole_0))),
% 2.27/2.50      inference('sup-', [status(thm)], ['117', '118'])).
% 2.27/2.50  thf('120', plain,
% 2.27/2.50      (![X8 : $i, X9 : $i]:
% 2.27/2.50         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 2.27/2.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.27/2.50  thf('121', plain,
% 2.27/2.50      ((((k1_xboole_0) != (k1_xboole_0))
% 2.27/2.50        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))),
% 2.27/2.50      inference('sup-', [status(thm)], ['119', '120'])).
% 2.27/2.50  thf('122', plain,
% 2.27/2.50      ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 2.27/2.50      inference('simplify', [status(thm)], ['121'])).
% 2.27/2.50  thf('123', plain,
% 2.27/2.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.27/2.50         (~ (r1_tarski @ X11 @ X12)
% 2.27/2.50          | (r1_tarski @ X11 @ (k2_xboole_0 @ X13 @ X12)))),
% 2.27/2.50      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.27/2.50  thf('124', plain,
% 2.27/2.50      (![X0 : $i]:
% 2.27/2.50         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 2.27/2.50          (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_B_1)))),
% 2.27/2.50      inference('sup-', [status(thm)], ['122', '123'])).
% 2.27/2.50  thf('125', plain,
% 2.27/2.50      ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 2.27/2.50      inference('sup+', [status(thm)], ['71', '124'])).
% 2.27/2.50  thf('126', plain,
% 2.27/2.50      ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 2.27/2.50      inference('demod', [status(thm)], ['47', '48'])).
% 2.27/2.50  thf('127', plain,
% 2.27/2.50      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.27/2.50         (~ (r1_tarski @ X24 @ X25)
% 2.27/2.50          | ~ (r1_tarski @ X26 @ X25)
% 2.27/2.50          | (r1_tarski @ (k2_xboole_0 @ X24 @ X26) @ X25))),
% 2.27/2.50      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.27/2.50  thf('128', plain,
% 2.27/2.50      (![X0 : $i]:
% 2.27/2.50         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 2.27/2.50           (k3_relat_1 @ sk_B_1))
% 2.27/2.50          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B_1)))),
% 2.27/2.50      inference('sup-', [status(thm)], ['126', '127'])).
% 2.27/2.50  thf('129', plain,
% 2.27/2.50      ((r1_tarski @ 
% 2.27/2.50        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 2.27/2.50        (k3_relat_1 @ sk_B_1))),
% 2.27/2.50      inference('sup-', [status(thm)], ['125', '128'])).
% 2.27/2.50  thf('130', plain,
% 2.27/2.50      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))
% 2.27/2.50        | ~ (v1_relat_1 @ sk_A))),
% 2.27/2.50      inference('sup+', [status(thm)], ['1', '129'])).
% 2.27/2.50  thf('131', plain, ((v1_relat_1 @ sk_A)),
% 2.27/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.50  thf('132', plain,
% 2.27/2.50      ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 2.27/2.50      inference('demod', [status(thm)], ['130', '131'])).
% 2.27/2.50  thf('133', plain, ($false), inference('demod', [status(thm)], ['0', '132'])).
% 2.27/2.50  
% 2.27/2.50  % SZS output end Refutation
% 2.27/2.50  
% 2.27/2.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
