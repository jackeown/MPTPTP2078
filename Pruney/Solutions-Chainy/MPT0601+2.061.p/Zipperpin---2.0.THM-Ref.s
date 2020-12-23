%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cc7v1DX2sF

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 257 expanded)
%              Number of leaves         :   20 (  80 expanded)
%              Depth                    :   16
%              Number of atoms          :  665 (2551 expanded)
%              Number of equality atoms :   42 ( 153 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k11_relat_1 @ X13 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 )
      | ( r2_hidden @ X5 @ X8 )
      | ( X8
       != ( k1_relat_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('7',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10
        = ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X10 @ X7 ) @ ( sk_D @ X10 @ X7 ) ) @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X7 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('14',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('16',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['15','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('28',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','31'])).

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

thf('33',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['35'])).

thf('39',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ ( sk_D_1 @ X9 @ X7 ) ) @ X7 )
      | ( X8
       != ( k1_relat_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('40',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X9 @ ( sk_D_1 @ X9 @ X7 ) ) @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X12 ) @ X13 )
      | ( r2_hidden @ X12 @ ( k11_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('43',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','45'])).

thf('47',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','45'])).

thf('48',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
        | ~ ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('51',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ X0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('54',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['36','52','53'])).

thf('55',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['34','54'])).

thf('56',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('60',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['36','52'])).

thf('61',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cc7v1DX2sF
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:59:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 56 iterations in 0.032s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(t3_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.48            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf(t204_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ C ) =>
% 0.21/0.48       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.21/0.48         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X12 @ (k11_relat_1 @ X13 @ X14))
% 0.21/0.48          | (r2_hidden @ (k4_tarski @ X14 @ X12) @ X13)
% 0.21/0.48          | ~ (v1_relat_1 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (k11_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | (r2_hidden @ 
% 0.21/0.48             (k4_tarski @ X0 @ (sk_C @ X2 @ (k11_relat_1 @ X1 @ X0))) @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf(d4_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.48       ( ![C:$i]:
% 0.21/0.48         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7)
% 0.21/0.48          | (r2_hidden @ X5 @ X8)
% 0.21/0.48          | ((X8) != (k1_relat_1 @ X7)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.48         ((r2_hidden @ X5 @ (k1_relat_1 @ X7))
% 0.21/0.48          | ~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.21/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | (r1_xboole_0 @ (k11_relat_1 @ X0 @ X1) @ X2)
% 0.21/0.48          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.48  thf(t60_relat_1, axiom,
% 0.21/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.48  thf('6', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X7 : $i, X10 : $i]:
% 0.21/0.48         (((X10) = (k1_relat_1 @ X7))
% 0.21/0.48          | (r2_hidden @ 
% 0.21/0.48             (k4_tarski @ (sk_C_1 @ X10 @ X7) @ (sk_D @ X10 @ X7)) @ X7)
% 0.21/0.48          | (r2_hidden @ (sk_C_1 @ X10 @ X7) @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.48         ((r2_hidden @ X5 @ (k1_relat_1 @ X7))
% 0.21/0.48          | ~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.21/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.21/0.48          | ((X1) = (k1_relat_1 @ X0))
% 0.21/0.48          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.48          | ((X0) = (k1_relat_1 @ k1_xboole_0))
% 0.21/0.48          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['6', '9'])).
% 0.21/0.48  thf('11', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.48          | ((X0) = (k1_xboole_0))
% 0.21/0.48          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.48          | ((X0) = (k1_xboole_0))
% 0.21/0.48          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.48          | ((X0) = (k1_xboole_0))
% 0.21/0.48          | ~ (r1_xboole_0 @ k1_xboole_0 @ X1)
% 0.21/0.48          | ~ (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.48  thf('16', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 0.21/0.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.48          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.21/0.48          | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.48  thf('23', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.48          | ((X0) = (k1_xboole_0))
% 0.21/0.48          | ~ (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1))),
% 0.21/0.48      inference('demod', [status(thm)], ['15', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.48          | ((X0) = (k1_xboole_0))
% 0.21/0.48          | ((X0) = (k1_xboole_0))
% 0.21/0.48          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((X0) = (k1_xboole_0))
% 0.21/0.48          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((X0) = (k1_xboole_0))
% 0.21/0.48          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((X0) = (k1_xboole_0))
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.48          | ~ (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((X0) = (k1_xboole_0))
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['26', '29'])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '31'])).
% 0.21/0.48  thf(t205_relat_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.48         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( v1_relat_1 @ B ) =>
% 0.21/0.48          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.48            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.21/0.48        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.21/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['33'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.21/0.48        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.48       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['35'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.21/0.48         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['33'])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['35'])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X9 @ X8)
% 0.21/0.48          | (r2_hidden @ (k4_tarski @ X9 @ (sk_D_1 @ X9 @ X7)) @ X7)
% 0.21/0.48          | ((X8) != (k1_relat_1 @ X7)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (![X7 : $i, X9 : $i]:
% 0.21/0.48         ((r2_hidden @ (k4_tarski @ X9 @ (sk_D_1 @ X9 @ X7)) @ X7)
% 0.21/0.48          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X7)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B)) @ sk_B))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['38', '40'])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.48         (~ (r2_hidden @ (k4_tarski @ X14 @ X12) @ X13)
% 0.21/0.48          | (r2_hidden @ X12 @ (k11_relat_1 @ X13 @ X14))
% 0.21/0.48          | ~ (v1_relat_1 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (((~ (v1_relat_1 @ sk_B)
% 0.21/0.48         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A))))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.48  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A)))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.48      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ k1_xboole_0))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.21/0.48             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup+', [status(thm)], ['37', '45'])).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ k1_xboole_0))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.21/0.48             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup+', [status(thm)], ['37', '45'])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      ((![X0 : $i]:
% 0.21/0.48          (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.48           | ~ (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ X0)))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.21/0.48             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.48  thf('50', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '22'])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      ((![X0 : $i]: ~ (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ X0))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.21/0.48             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.21/0.48       ~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['46', '51'])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.21/0.48       (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('split', [status(esa)], ['33'])).
% 0.21/0.48  thf('54', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['36', '52', '53'])).
% 0.21/0.48  thf('55', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['34', '54'])).
% 0.21/0.48  thf('56', plain,
% 0.21/0.48      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['32', '55'])).
% 0.21/0.48  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('58', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.48  thf('59', plain,
% 0.21/0.48      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['35'])).
% 0.21/0.48  thf('60', plain, (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['36', '52'])).
% 0.21/0.48  thf('61', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.21/0.48  thf('62', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['58', '61'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
