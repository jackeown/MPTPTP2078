%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RSrYxCP8b4

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:46 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 249 expanded)
%              Number of leaves         :   23 (  84 expanded)
%              Depth                    :   18
%              Number of atoms          :  670 (1845 expanded)
%              Number of equality atoms :   43 ( 123 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('5',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','5'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15
        = ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X15 @ X12 ) @ ( sk_D @ X15 @ X12 ) ) @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X12 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('9',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('12',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15
        = ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X15 @ X12 ) @ ( sk_D @ X15 @ X12 ) ) @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X12 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('15',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15
        = ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X15 @ X12 ) @ ( sk_D @ X15 @ X12 ) ) @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X12 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('19',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ ( k1_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['13','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('31',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('34',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('37',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D_1 @ X14 @ X12 ) ) @ X12 )
      | ( X13
       != ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('38',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D_1 @ X14 @ X12 ) ) @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X17 ) @ X18 )
      | ( r2_hidden @ X17 @ ( k11_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('41',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','5'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['33','48'])).

thf('50',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['32','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k1_relat_1 @ X0 ) )
       != k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) @ k1_xboole_0 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('54',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) @ k1_xboole_0 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['51','58'])).

thf('60',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k11_relat_1 @ X18 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C_1 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) @ k1_xboole_0 ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C_1 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) @ k1_xboole_0 ) ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X10 @ X13 )
      | ( X13
       != ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('65',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['34'])).

thf('68',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('69',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['33','48','68'])).

thf('70',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['66','70'])).

thf('72',plain,(
    $false ),
    inference('sup-',[status(thm)],['6','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RSrYxCP8b4
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:11:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.50/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.68  % Solved by: fo/fo7.sh
% 0.50/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.68  % done 423 iterations in 0.221s
% 0.50/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.68  % SZS output start Refutation
% 0.50/0.68  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.50/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.68  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.50/0.68  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.50/0.68  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.50/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.50/0.68  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.50/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.50/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.50/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.50/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.68  thf(d1_xboole_0, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.50/0.68  thf('0', plain,
% 0.50/0.68      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.50/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.50/0.68  thf(t2_boole, axiom,
% 0.50/0.68    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.50/0.68  thf('1', plain,
% 0.50/0.68      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.68      inference('cnf', [status(esa)], [t2_boole])).
% 0.50/0.68  thf(t4_xboole_0, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.50/0.68            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.50/0.68       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.50/0.68            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.50/0.68  thf('2', plain,
% 0.50/0.68      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.50/0.68          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.50/0.68      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.50/0.68  thf('3', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.68  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.50/0.68  thf('4', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.50/0.68      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.50/0.68  thf('5', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.50/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.50/0.68  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.50/0.68      inference('sup-', [status(thm)], ['0', '5'])).
% 0.50/0.68  thf(l13_xboole_0, axiom,
% 0.50/0.68    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.50/0.68  thf('7', plain,
% 0.50/0.68      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.50/0.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.50/0.68  thf(d4_relat_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.50/0.68       ( ![C:$i]:
% 0.50/0.68         ( ( r2_hidden @ C @ B ) <=>
% 0.50/0.68           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.50/0.68  thf('8', plain,
% 0.50/0.68      (![X12 : $i, X15 : $i]:
% 0.50/0.68         (((X15) = (k1_relat_1 @ X12))
% 0.50/0.68          | (r2_hidden @ 
% 0.50/0.68             (k4_tarski @ (sk_C_1 @ X15 @ X12) @ (sk_D @ X15 @ X12)) @ X12)
% 0.50/0.68          | (r2_hidden @ (sk_C_1 @ X15 @ X12) @ X15))),
% 0.50/0.68      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.50/0.68  thf('9', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.50/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.50/0.68  thf('10', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.50/0.68          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.50/0.68  thf('11', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.50/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.50/0.68  thf('12', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.50/0.68  thf('13', plain,
% 0.50/0.68      (![X0 : $i]: (((k1_xboole_0) = (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['7', '12'])).
% 0.50/0.68  thf('14', plain,
% 0.50/0.68      (![X12 : $i, X15 : $i]:
% 0.50/0.68         (((X15) = (k1_relat_1 @ X12))
% 0.50/0.68          | (r2_hidden @ 
% 0.50/0.68             (k4_tarski @ (sk_C_1 @ X15 @ X12) @ (sk_D @ X15 @ X12)) @ X12)
% 0.50/0.68          | (r2_hidden @ (sk_C_1 @ X15 @ X12) @ X15))),
% 0.50/0.68      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.50/0.68  thf('15', plain,
% 0.50/0.68      (![X12 : $i, X15 : $i]:
% 0.50/0.68         (((X15) = (k1_relat_1 @ X12))
% 0.50/0.68          | (r2_hidden @ 
% 0.50/0.68             (k4_tarski @ (sk_C_1 @ X15 @ X12) @ (sk_D @ X15 @ X12)) @ X12)
% 0.50/0.68          | (r2_hidden @ (sk_C_1 @ X15 @ X12) @ X15))),
% 0.50/0.68      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.50/0.68  thf('16', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.50/0.68  thf('17', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.50/0.68          | ((X1) = (k1_relat_1 @ X0))
% 0.50/0.68          | ~ (v1_xboole_0 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.50/0.68  thf('18', plain,
% 0.50/0.68      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.50/0.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.50/0.68  thf('19', plain,
% 0.50/0.68      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.68      inference('cnf', [status(esa)], [t2_boole])).
% 0.50/0.68  thf('20', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['18', '19'])).
% 0.50/0.68  thf('21', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.50/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.50/0.68  thf('22', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['20', '21'])).
% 0.50/0.68  thf('23', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.68         (~ (v1_xboole_0 @ X2)
% 0.50/0.68          | ((k3_xboole_0 @ X1 @ X0) = (k1_relat_1 @ X2))
% 0.50/0.68          | ~ (v1_xboole_0 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['17', '22'])).
% 0.50/0.68  thf('24', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['20', '21'])).
% 0.50/0.68  thf('25', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X3 @ (k1_relat_1 @ X0))
% 0.50/0.68          | ~ (v1_xboole_0 @ X1)
% 0.50/0.68          | ~ (v1_xboole_0 @ X0)
% 0.50/0.68          | ~ (v1_xboole_0 @ X1))),
% 0.50/0.68      inference('sup-', [status(thm)], ['23', '24'])).
% 0.50/0.68  thf('26', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.50/0.68         (~ (v1_xboole_0 @ X0)
% 0.50/0.68          | ~ (v1_xboole_0 @ X1)
% 0.50/0.68          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ X0)))),
% 0.50/0.68      inference('simplify', [status(thm)], ['25'])).
% 0.50/0.68  thf('27', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.68      inference('condensation', [status(thm)], ['26'])).
% 0.50/0.68  thf('28', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((r2_hidden @ (sk_C_1 @ X1 @ (k1_relat_1 @ X0)) @ X1)
% 0.50/0.68          | ((X1) = (k1_relat_1 @ (k1_relat_1 @ X0)))
% 0.50/0.68          | ~ (v1_xboole_0 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['14', '27'])).
% 0.50/0.68  thf('29', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.50/0.68          | ~ (v1_xboole_0 @ X1)
% 0.50/0.68          | ~ (v1_xboole_0 @ X1)
% 0.50/0.68          | ((X0) = (k1_relat_1 @ (k1_relat_1 @ X1))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['13', '28'])).
% 0.50/0.68  thf('30', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         (((X0) = (k1_relat_1 @ (k1_relat_1 @ X1)))
% 0.50/0.68          | ~ (v1_xboole_0 @ X1)
% 0.50/0.68          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.50/0.68      inference('simplify', [status(thm)], ['29'])).
% 0.50/0.68  thf(t205_relat_1, conjecture,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( v1_relat_1 @ B ) =>
% 0.50/0.68       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.50/0.68         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.50/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.68    (~( ![A:$i,B:$i]:
% 0.50/0.68        ( ( v1_relat_1 @ B ) =>
% 0.50/0.68          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.50/0.68            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.50/0.68    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.50/0.68  thf('31', plain,
% 0.50/0.68      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.50/0.68        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('32', plain,
% 0.50/0.68      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.50/0.68         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.50/0.68      inference('split', [status(esa)], ['31'])).
% 0.50/0.68  thf('33', plain,
% 0.50/0.68      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.50/0.68       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.50/0.68      inference('split', [status(esa)], ['31'])).
% 0.50/0.68  thf('34', plain,
% 0.50/0.68      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.50/0.68        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('35', plain,
% 0.50/0.68      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.50/0.68         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.50/0.68      inference('split', [status(esa)], ['34'])).
% 0.50/0.68  thf('36', plain,
% 0.50/0.68      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.50/0.68         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.50/0.68      inference('split', [status(esa)], ['31'])).
% 0.50/0.68  thf('37', plain,
% 0.50/0.68      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X14 @ X13)
% 0.50/0.68          | (r2_hidden @ (k4_tarski @ X14 @ (sk_D_1 @ X14 @ X12)) @ X12)
% 0.50/0.68          | ((X13) != (k1_relat_1 @ X12)))),
% 0.50/0.68      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.50/0.68  thf('38', plain,
% 0.50/0.68      (![X12 : $i, X14 : $i]:
% 0.50/0.68         ((r2_hidden @ (k4_tarski @ X14 @ (sk_D_1 @ X14 @ X12)) @ X12)
% 0.50/0.68          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X12)))),
% 0.50/0.68      inference('simplify', [status(thm)], ['37'])).
% 0.50/0.68  thf('39', plain,
% 0.50/0.68      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B_1)) @ sk_B_1))
% 0.50/0.68         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['36', '38'])).
% 0.50/0.68  thf(t204_relat_1, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i]:
% 0.50/0.68     ( ( v1_relat_1 @ C ) =>
% 0.50/0.68       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.50/0.68         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.50/0.68  thf('40', plain,
% 0.50/0.68      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.50/0.68         (~ (r2_hidden @ (k4_tarski @ X19 @ X17) @ X18)
% 0.50/0.68          | (r2_hidden @ X17 @ (k11_relat_1 @ X18 @ X19))
% 0.50/0.68          | ~ (v1_relat_1 @ X18))),
% 0.50/0.68      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.50/0.68  thf('41', plain,
% 0.50/0.68      (((~ (v1_relat_1 @ sk_B_1)
% 0.50/0.68         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ 
% 0.50/0.68            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.50/0.68         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['39', '40'])).
% 0.50/0.68  thf('42', plain, ((v1_relat_1 @ sk_B_1)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('43', plain,
% 0.50/0.68      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.50/0.68         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.50/0.68      inference('demod', [status(thm)], ['41', '42'])).
% 0.50/0.68  thf('44', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.50/0.68  thf('45', plain,
% 0.50/0.68      ((~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.50/0.68         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['43', '44'])).
% 0.50/0.68  thf('46', plain,
% 0.50/0.68      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.50/0.68         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.50/0.68             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['35', '45'])).
% 0.50/0.68  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.50/0.68      inference('sup-', [status(thm)], ['0', '5'])).
% 0.50/0.68  thf('48', plain,
% 0.50/0.68      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.50/0.68       ~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.50/0.68      inference('demod', [status(thm)], ['46', '47'])).
% 0.50/0.68  thf('49', plain, (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.50/0.68      inference('sat_resolution*', [status(thm)], ['33', '48'])).
% 0.50/0.68  thf('50', plain, (((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))),
% 0.50/0.68      inference('simpl_trail', [status(thm)], ['32', '49'])).
% 0.50/0.68  thf('51', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (((k1_relat_1 @ (k1_relat_1 @ X0)) != (k1_xboole_0))
% 0.50/0.68          | (r2_hidden @ 
% 0.50/0.68             (sk_C_1 @ (k11_relat_1 @ sk_B_1 @ sk_A) @ k1_xboole_0) @ 
% 0.50/0.68             (k11_relat_1 @ sk_B_1 @ sk_A))
% 0.50/0.68          | ~ (v1_xboole_0 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['30', '50'])).
% 0.50/0.68  thf('52', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.68         (~ (v1_xboole_0 @ X2)
% 0.50/0.68          | ((k3_xboole_0 @ X1 @ X0) = (k1_relat_1 @ X2))
% 0.50/0.68          | ~ (v1_xboole_0 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['17', '22'])).
% 0.50/0.68  thf('53', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['18', '19'])).
% 0.50/0.68  thf('54', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.50/0.68  thf('55', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         (((k1_xboole_0) = (k1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.50/0.68          | ~ (v1_xboole_0 @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['53', '54'])).
% 0.50/0.68  thf('56', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         (((k1_xboole_0) = (k1_relat_1 @ (k1_relat_1 @ X0)))
% 0.50/0.68          | ~ (v1_xboole_0 @ X1)
% 0.50/0.68          | ~ (v1_xboole_0 @ X0)
% 0.50/0.68          | ~ (v1_xboole_0 @ X1))),
% 0.50/0.68      inference('sup+', [status(thm)], ['52', '55'])).
% 0.50/0.68  thf('57', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         (~ (v1_xboole_0 @ X0)
% 0.50/0.68          | ~ (v1_xboole_0 @ X1)
% 0.50/0.68          | ((k1_xboole_0) = (k1_relat_1 @ (k1_relat_1 @ X0))))),
% 0.50/0.68      inference('simplify', [status(thm)], ['56'])).
% 0.50/0.68  thf('58', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (((k1_xboole_0) = (k1_relat_1 @ (k1_relat_1 @ X0)))
% 0.50/0.68          | ~ (v1_xboole_0 @ X0))),
% 0.50/0.68      inference('condensation', [status(thm)], ['57'])).
% 0.50/0.68  thf('59', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (~ (v1_xboole_0 @ X0)
% 0.50/0.68          | (r2_hidden @ 
% 0.50/0.68             (sk_C_1 @ (k11_relat_1 @ sk_B_1 @ sk_A) @ k1_xboole_0) @ 
% 0.50/0.68             (k11_relat_1 @ sk_B_1 @ sk_A)))),
% 0.50/0.68      inference('clc', [status(thm)], ['51', '58'])).
% 0.50/0.68  thf('60', plain,
% 0.50/0.68      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X17 @ (k11_relat_1 @ X18 @ X19))
% 0.50/0.68          | (r2_hidden @ (k4_tarski @ X19 @ X17) @ X18)
% 0.50/0.68          | ~ (v1_relat_1 @ X18))),
% 0.50/0.68      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.50/0.68  thf('61', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (~ (v1_xboole_0 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ sk_B_1)
% 0.50/0.68          | (r2_hidden @ 
% 0.50/0.68             (k4_tarski @ sk_A @ 
% 0.50/0.68              (sk_C_1 @ (k11_relat_1 @ sk_B_1 @ sk_A) @ k1_xboole_0)) @ 
% 0.50/0.68             sk_B_1))),
% 0.50/0.68      inference('sup-', [status(thm)], ['59', '60'])).
% 0.50/0.68  thf('62', plain, ((v1_relat_1 @ sk_B_1)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('63', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (~ (v1_xboole_0 @ X0)
% 0.50/0.68          | (r2_hidden @ 
% 0.50/0.68             (k4_tarski @ sk_A @ 
% 0.50/0.68              (sk_C_1 @ (k11_relat_1 @ sk_B_1 @ sk_A) @ k1_xboole_0)) @ 
% 0.50/0.68             sk_B_1))),
% 0.50/0.68      inference('demod', [status(thm)], ['61', '62'])).
% 0.50/0.68  thf('64', plain,
% 0.50/0.68      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.50/0.68         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.50/0.68          | (r2_hidden @ X10 @ X13)
% 0.50/0.68          | ((X13) != (k1_relat_1 @ X12)))),
% 0.50/0.68      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.50/0.68  thf('65', plain,
% 0.50/0.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.50/0.68         ((r2_hidden @ X10 @ (k1_relat_1 @ X12))
% 0.50/0.68          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.50/0.68      inference('simplify', [status(thm)], ['64'])).
% 0.50/0.68  thf('66', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (~ (v1_xboole_0 @ X0) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['63', '65'])).
% 0.50/0.68  thf('67', plain,
% 0.50/0.68      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.50/0.68         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.50/0.68      inference('split', [status(esa)], ['34'])).
% 0.50/0.68  thf('68', plain,
% 0.50/0.68      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.50/0.68       (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.50/0.68      inference('split', [status(esa)], ['34'])).
% 0.50/0.68  thf('69', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.50/0.68      inference('sat_resolution*', [status(thm)], ['33', '48', '68'])).
% 0.50/0.68  thf('70', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.50/0.68      inference('simpl_trail', [status(thm)], ['67', '69'])).
% 0.50/0.68  thf('71', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.50/0.68      inference('clc', [status(thm)], ['66', '70'])).
% 0.50/0.68  thf('72', plain, ($false), inference('sup-', [status(thm)], ['6', '71'])).
% 0.50/0.68  
% 0.50/0.68  % SZS output end Refutation
% 0.50/0.68  
% 0.50/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
