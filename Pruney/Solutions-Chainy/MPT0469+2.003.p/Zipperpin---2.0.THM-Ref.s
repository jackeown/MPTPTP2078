%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9hnjiJ9dG4

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:17 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 193 expanded)
%              Number of leaves         :   37 (  76 expanded)
%              Depth                    :   19
%              Number of atoms          :  585 ( 972 expanded)
%              Number of equality atoms :   72 ( 129 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28
        = ( k1_relat_1 @ X25 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X28 @ X25 ) @ ( sk_D @ X28 @ X25 ) ) @ X25 )
      | ( r2_hidden @ ( sk_C_2 @ X28 @ X25 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('8',plain,(
    ! [X21: $i] :
      ( r1_xboole_0 @ X21 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    ! [X21: $i] :
      ( r1_xboole_0 @ X21 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ o_0_0_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ o_0_0_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('14',plain,
    ( o_0_0_xboole_0
    = ( k1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X33: $i] :
      ( ( ( k1_relat_1 @ X33 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('16',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('19',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('20',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ o_0_0_xboole_0 )
      = X16 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(t26_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X32 @ X31 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X32 ) @ ( k2_relat_1 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

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

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('31',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('32',plain,(
    ! [X5: $i] :
      ( ( X5 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k5_xboole_0 @ X1 @ o_0_0_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('37',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('38',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ o_0_0_xboole_0 )
      = X20 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('40',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('41',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X1 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ o_0_0_xboole_0 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','44'])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('46',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('49',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('50',plain,
    ( ( ( k2_relat_1 @ o_0_0_xboole_0 )
     != o_0_0_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( o_0_0_xboole_0
    = ( k1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('52',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('53',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('54',plain,
    ( ( ( k1_relat_1 @ o_0_0_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('56',plain,
    ( ( ( k1_relat_1 @ o_0_0_xboole_0 )
     != o_0_0_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('60',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('61',plain,(
    ( k2_relat_1 @ o_0_0_xboole_0 )
 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['50','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','62'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('66',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','67'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('69',plain,(
    ! [X30: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','70'])).

thf('72',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['64','65'])).

thf('73',plain,(
    ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','73'])).

thf('75',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['64','65'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9hnjiJ9dG4
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 193 iterations in 0.063s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.54  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.37/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.37/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.37/0.54  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.37/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.54  thf(cc1_relat_1, axiom,
% 0.37/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.37/0.54  thf('0', plain, (![X22 : $i]: ((v1_relat_1 @ X22) | ~ (v1_xboole_0 @ X22))),
% 0.37/0.54      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.37/0.54  thf(d4_relat_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.37/0.54       ( ![C:$i]:
% 0.37/0.54         ( ( r2_hidden @ C @ B ) <=>
% 0.37/0.54           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      (![X25 : $i, X28 : $i]:
% 0.37/0.54         (((X28) = (k1_relat_1 @ X25))
% 0.37/0.54          | (r2_hidden @ 
% 0.37/0.54             (k4_tarski @ (sk_C_2 @ X28 @ X25) @ (sk_D @ X28 @ X25)) @ X25)
% 0.37/0.54          | (r2_hidden @ (sk_C_2 @ X28 @ X25) @ X28))),
% 0.37/0.54      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.37/0.54  thf(t2_boole, axiom,
% 0.37/0.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.37/0.54  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.37/0.54  thf('3', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.37/0.54  thf('4', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.37/0.54  thf('5', plain,
% 0.37/0.54      (![X17 : $i]: ((k3_xboole_0 @ X17 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.37/0.54      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.37/0.54  thf(t4_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.37/0.54          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.37/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.54  thf('7', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X1 @ o_0_0_xboole_0)
% 0.37/0.54          | ~ (r1_xboole_0 @ X0 @ o_0_0_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.54  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.37/0.54  thf('8', plain, (![X21 : $i]: (r1_xboole_0 @ X21 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.54  thf('9', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.37/0.54  thf('10', plain, (![X21 : $i]: (r1_xboole_0 @ X21 @ o_0_0_xboole_0)),
% 0.37/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.37/0.54  thf('11', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ o_0_0_xboole_0)),
% 0.37/0.54      inference('demod', [status(thm)], ['7', '10'])).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r2_hidden @ (sk_C_2 @ X0 @ o_0_0_xboole_0) @ X0)
% 0.37/0.54          | ((X0) = (k1_relat_1 @ o_0_0_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['1', '11'])).
% 0.37/0.54  thf('13', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ o_0_0_xboole_0)),
% 0.37/0.54      inference('demod', [status(thm)], ['7', '10'])).
% 0.37/0.54  thf('14', plain, (((o_0_0_xboole_0) = (k1_relat_1 @ o_0_0_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.54  thf(t37_relat_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( v1_relat_1 @ A ) =>
% 0.37/0.54       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.37/0.54         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      (![X33 : $i]:
% 0.37/0.54         (((k1_relat_1 @ X33) = (k2_relat_1 @ (k4_relat_1 @ X33)))
% 0.37/0.54          | ~ (v1_relat_1 @ X33))),
% 0.37/0.54      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.37/0.54  thf('16', plain, (![X22 : $i]: ((v1_relat_1 @ X22) | ~ (v1_xboole_0 @ X22))),
% 0.37/0.54      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.37/0.54  thf(commutativity_k2_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.37/0.54  thf('17', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.54  thf(t1_boole, axiom,
% 0.37/0.54    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.54  thf('18', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.37/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.54  thf('19', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.37/0.54  thf('20', plain,
% 0.37/0.54      (![X16 : $i]: ((k2_xboole_0 @ X16 @ o_0_0_xboole_0) = (X16))),
% 0.37/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.54  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ o_0_0_xboole_0 @ X0) = (X0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['17', '20'])).
% 0.37/0.54  thf(t26_relat_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( v1_relat_1 @ A ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( v1_relat_1 @ B ) =>
% 0.37/0.54           ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 0.37/0.54             ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.37/0.54  thf('22', plain,
% 0.37/0.54      (![X31 : $i, X32 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X31)
% 0.37/0.54          | ((k2_relat_1 @ (k2_xboole_0 @ X32 @ X31))
% 0.37/0.54              = (k2_xboole_0 @ (k2_relat_1 @ X32) @ (k2_relat_1 @ X31)))
% 0.37/0.54          | ~ (v1_relat_1 @ X32))),
% 0.37/0.54      inference('cnf', [status(esa)], [t26_relat_1])).
% 0.37/0.54  thf(t3_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.37/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.37/0.54  thf('23', plain,
% 0.37/0.54      (![X6 : $i, X7 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.37/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.54  thf(d1_xboole_0, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.54  thf('24', plain,
% 0.37/0.54      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.37/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.54  thf('25', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.54  thf('26', plain,
% 0.37/0.54      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.37/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.54  thf('27', plain,
% 0.37/0.54      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.37/0.54          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.37/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.54  thf('28', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.54  thf('29', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['25', '28'])).
% 0.37/0.54  thf(l13_xboole_0, axiom,
% 0.37/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.54  thf('30', plain,
% 0.37/0.54      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 0.37/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.54  thf('31', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.37/0.54  thf('32', plain,
% 0.37/0.54      (![X5 : $i]: (((X5) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 0.37/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.37/0.54  thf('33', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ X0) | ((k3_xboole_0 @ X1 @ X0) = (o_0_0_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['29', '32'])).
% 0.37/0.54  thf(t100_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.54  thf('34', plain,
% 0.37/0.54      (![X14 : $i, X15 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ X14 @ X15)
% 0.37/0.54           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.54  thf('35', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X1 @ o_0_0_xboole_0))
% 0.37/0.54          | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['33', '34'])).
% 0.37/0.54  thf(t5_boole, axiom,
% 0.37/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.54  thf('36', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.37/0.54      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.54  thf('37', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.37/0.54  thf('38', plain,
% 0.37/0.54      (![X20 : $i]: ((k5_xboole_0 @ X20 @ o_0_0_xboole_0) = (X20))),
% 0.37/0.54      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.54  thf('39', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('demod', [status(thm)], ['35', '38'])).
% 0.37/0.54  thf(t46_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.37/0.54  thf('40', plain,
% 0.37/0.54      (![X18 : $i, X19 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.37/0.54  thf('41', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.37/0.54  thf('42', plain,
% 0.37/0.54      (![X18 : $i, X19 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (o_0_0_xboole_0))),
% 0.37/0.54      inference('demod', [status(thm)], ['40', '41'])).
% 0.37/0.54  thf('43', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((X0) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.37/0.54      inference('sup+', [status(thm)], ['39', '42'])).
% 0.37/0.54  thf('44', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.37/0.54          | ~ (v1_relat_1 @ X1)
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | ((k2_relat_1 @ X1) = (o_0_0_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['22', '43'])).
% 0.37/0.54  thf('45', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.37/0.54          | ((k2_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['21', '44'])).
% 0.37/0.54  thf(t60_relat_1, conjecture,
% 0.37/0.54    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.37/0.54     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.37/0.54        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.37/0.54  thf('46', plain,
% 0.37/0.54      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.37/0.54        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('47', plain,
% 0.37/0.54      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.54         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.54      inference('split', [status(esa)], ['46'])).
% 0.37/0.54  thf('48', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.37/0.54  thf('49', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.37/0.54  thf('50', plain,
% 0.37/0.54      ((((k2_relat_1 @ o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.37/0.54         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.54      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.37/0.54  thf('51', plain, (((o_0_0_xboole_0) = (k1_relat_1 @ o_0_0_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.54  thf('52', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.37/0.54  thf('53', plain,
% 0.37/0.54      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.54         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.54      inference('split', [status(esa)], ['46'])).
% 0.37/0.54  thf('54', plain,
% 0.37/0.54      ((((k1_relat_1 @ o_0_0_xboole_0) != (k1_xboole_0)))
% 0.37/0.54         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.54  thf('55', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.37/0.54  thf('56', plain,
% 0.37/0.54      ((((k1_relat_1 @ o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.37/0.54         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.37/0.54  thf('57', plain,
% 0.37/0.54      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.37/0.54         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['51', '56'])).
% 0.37/0.54  thf('58', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['57'])).
% 0.37/0.54  thf('59', plain,
% 0.37/0.54      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.37/0.54       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.54      inference('split', [status(esa)], ['46'])).
% 0.37/0.54  thf('60', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.54      inference('sat_resolution*', [status(thm)], ['58', '59'])).
% 0.37/0.54  thf('61', plain, (((k2_relat_1 @ o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.37/0.54      inference('simpl_trail', [status(thm)], ['50', '60'])).
% 0.37/0.54  thf('62', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['45', '61'])).
% 0.37/0.54  thf('63', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ o_0_0_xboole_0)
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['16', '62'])).
% 0.37/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.54  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.54  thf('65', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.37/0.54  thf('66', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.37/0.54      inference('demod', [status(thm)], ['64', '65'])).
% 0.37/0.54  thf('67', plain,
% 0.37/0.54      (![X0 : $i]: (~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.37/0.54      inference('demod', [status(thm)], ['63', '66'])).
% 0.37/0.54  thf('68', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['15', '67'])).
% 0.37/0.54  thf(dt_k4_relat_1, axiom,
% 0.37/0.54    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.37/0.54  thf('69', plain,
% 0.37/0.54      (![X30 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X30)) | ~ (v1_relat_1 @ X30))),
% 0.37/0.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.37/0.54  thf('70', plain,
% 0.37/0.54      (![X0 : $i]: (~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.37/0.54      inference('clc', [status(thm)], ['68', '69'])).
% 0.37/0.54  thf('71', plain,
% 0.37/0.54      ((~ (v1_xboole_0 @ o_0_0_xboole_0) | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['14', '70'])).
% 0.37/0.54  thf('72', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.37/0.54      inference('demod', [status(thm)], ['64', '65'])).
% 0.37/0.54  thf('73', plain, (~ (v1_relat_1 @ o_0_0_xboole_0)),
% 0.37/0.54      inference('demod', [status(thm)], ['71', '72'])).
% 0.37/0.54  thf('74', plain, (~ (v1_xboole_0 @ o_0_0_xboole_0)),
% 0.37/0.54      inference('sup-', [status(thm)], ['0', '73'])).
% 0.37/0.54  thf('75', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.37/0.54      inference('demod', [status(thm)], ['64', '65'])).
% 0.37/0.54  thf('76', plain, ($false), inference('demod', [status(thm)], ['74', '75'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
