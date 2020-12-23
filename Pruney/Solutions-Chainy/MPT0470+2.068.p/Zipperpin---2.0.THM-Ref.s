%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uDd67S3mbO

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:36 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 257 expanded)
%              Number of leaves         :   28 (  90 expanded)
%              Depth                    :   22
%              Number of atoms          :  786 (1705 expanded)
%              Number of equality atoms :   79 ( 195 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X28: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X28 ) )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X26 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('4',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X32 @ X31 ) )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('9',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X27: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','19'])).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t41_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) )
            = ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) )).

thf('33',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ X30 @ X29 ) )
        = ( k6_subset_1 @ ( k4_relat_1 @ X30 ) @ ( k4_relat_1 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t41_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('35',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('36',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X30 @ X29 ) )
        = ( k4_xboole_0 @ ( k4_relat_1 @ X30 ) @ ( k4_relat_1 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','40'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X34 @ X33 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X33 ) @ ( k4_relat_1 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('52',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('54',plain,(
    ! [X24: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','66'])).

thf('68',plain,(
    ! [X24: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('75',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('76',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('87',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['73','87'])).

thf('89',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('92',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    $false ),
    inference(simplify,[status(thm)],['92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uDd67S3mbO
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.65/1.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.88  % Solved by: fo/fo7.sh
% 1.65/1.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.88  % done 2737 iterations in 1.430s
% 1.65/1.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.88  % SZS output start Refutation
% 1.65/1.88  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.65/1.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.65/1.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.88  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.65/1.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.65/1.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.65/1.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.65/1.88  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.88  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.65/1.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.65/1.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.65/1.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.65/1.88  thf(involutiveness_k4_relat_1, axiom,
% 1.65/1.88    (![A:$i]:
% 1.65/1.88     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 1.65/1.88  thf('0', plain,
% 1.65/1.88      (![X28 : $i]:
% 1.65/1.88         (((k4_relat_1 @ (k4_relat_1 @ X28)) = (X28)) | ~ (v1_relat_1 @ X28))),
% 1.65/1.88      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 1.65/1.88  thf(l13_xboole_0, axiom,
% 1.65/1.88    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.65/1.88  thf('1', plain,
% 1.65/1.88      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.65/1.88  thf(cc1_relat_1, axiom,
% 1.65/1.88    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 1.65/1.88  thf('2', plain, (![X23 : $i]: ((v1_relat_1 @ X23) | ~ (v1_xboole_0 @ X23))),
% 1.65/1.88      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.65/1.88  thf(dt_k5_relat_1, axiom,
% 1.65/1.88    (![A:$i,B:$i]:
% 1.65/1.88     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.65/1.88       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.65/1.88  thf('3', plain,
% 1.65/1.88      (![X25 : $i, X26 : $i]:
% 1.65/1.88         (~ (v1_relat_1 @ X25)
% 1.65/1.88          | ~ (v1_relat_1 @ X26)
% 1.65/1.88          | (v1_relat_1 @ (k5_relat_1 @ X25 @ X26)))),
% 1.65/1.88      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.65/1.88  thf('4', plain, (![X23 : $i]: ((v1_relat_1 @ X23) | ~ (v1_xboole_0 @ X23))),
% 1.65/1.88      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.65/1.88  thf(t60_relat_1, axiom,
% 1.65/1.88    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.65/1.88     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.65/1.88  thf('5', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.88      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.65/1.88  thf(t46_relat_1, axiom,
% 1.65/1.88    (![A:$i]:
% 1.65/1.88     ( ( v1_relat_1 @ A ) =>
% 1.65/1.88       ( ![B:$i]:
% 1.65/1.88         ( ( v1_relat_1 @ B ) =>
% 1.65/1.88           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 1.65/1.88             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 1.65/1.88  thf('6', plain,
% 1.65/1.88      (![X31 : $i, X32 : $i]:
% 1.65/1.88         (~ (v1_relat_1 @ X31)
% 1.65/1.88          | ((k1_relat_1 @ (k5_relat_1 @ X32 @ X31)) = (k1_relat_1 @ X32))
% 1.65/1.88          | ~ (r1_tarski @ (k2_relat_1 @ X32) @ (k1_relat_1 @ X31))
% 1.65/1.88          | ~ (v1_relat_1 @ X32))),
% 1.65/1.88      inference('cnf', [status(esa)], [t46_relat_1])).
% 1.65/1.88  thf('7', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 1.65/1.88          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.65/1.88          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.65/1.88              = (k1_relat_1 @ k1_xboole_0))
% 1.65/1.88          | ~ (v1_relat_1 @ X0))),
% 1.65/1.88      inference('sup-', [status(thm)], ['5', '6'])).
% 1.65/1.88  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.65/1.88  thf('8', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 1.65/1.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.65/1.88  thf('9', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.88      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.65/1.88  thf('10', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (v1_relat_1 @ k1_xboole_0)
% 1.65/1.88          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 1.65/1.88          | ~ (v1_relat_1 @ X0))),
% 1.65/1.88      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.65/1.88  thf('11', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.65/1.88          | ~ (v1_relat_1 @ X0)
% 1.65/1.88          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 1.65/1.88      inference('sup-', [status(thm)], ['4', '10'])).
% 1.65/1.88  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.65/1.88  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.88  thf('13', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (v1_relat_1 @ X0)
% 1.65/1.88          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 1.65/1.88      inference('demod', [status(thm)], ['11', '12'])).
% 1.65/1.88  thf(fc8_relat_1, axiom,
% 1.65/1.88    (![A:$i]:
% 1.65/1.88     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 1.65/1.88       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 1.65/1.88  thf('14', plain,
% 1.65/1.88      (![X27 : $i]:
% 1.65/1.88         (~ (v1_xboole_0 @ (k1_relat_1 @ X27))
% 1.65/1.88          | ~ (v1_relat_1 @ X27)
% 1.65/1.88          | (v1_xboole_0 @ X27))),
% 1.65/1.88      inference('cnf', [status(esa)], [fc8_relat_1])).
% 1.65/1.88  thf('15', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.65/1.88          | ~ (v1_relat_1 @ X0)
% 1.65/1.88          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.65/1.88          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.65/1.88      inference('sup-', [status(thm)], ['13', '14'])).
% 1.65/1.88  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.88  thf('17', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (v1_relat_1 @ X0)
% 1.65/1.88          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.65/1.88          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.65/1.88      inference('demod', [status(thm)], ['15', '16'])).
% 1.65/1.88  thf('18', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (v1_relat_1 @ X0)
% 1.65/1.88          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.65/1.88          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.65/1.88          | ~ (v1_relat_1 @ X0))),
% 1.65/1.88      inference('sup-', [status(thm)], ['3', '17'])).
% 1.65/1.88  thf('19', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.65/1.88          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.65/1.88          | ~ (v1_relat_1 @ X0))),
% 1.65/1.88      inference('simplify', [status(thm)], ['18'])).
% 1.65/1.88  thf('20', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.65/1.88          | ~ (v1_relat_1 @ X0)
% 1.65/1.88          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.65/1.88      inference('sup-', [status(thm)], ['2', '19'])).
% 1.65/1.88  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.88  thf('22', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.65/1.88      inference('demod', [status(thm)], ['20', '21'])).
% 1.65/1.88  thf(idempotence_k2_xboole_0, axiom,
% 1.65/1.88    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.65/1.88  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.65/1.88      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.65/1.88  thf(t46_xboole_1, axiom,
% 1.65/1.88    (![A:$i,B:$i]:
% 1.65/1.88     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.65/1.88  thf('24', plain,
% 1.65/1.88      (![X3 : $i, X4 : $i]:
% 1.65/1.88         ((k4_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (k1_xboole_0))),
% 1.65/1.88      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.65/1.88  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['23', '24'])).
% 1.65/1.88  thf('26', plain,
% 1.65/1.88      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.65/1.88  thf('27', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         (((X1) = (k4_xboole_0 @ X0 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.88      inference('sup+', [status(thm)], ['25', '26'])).
% 1.65/1.88  thf('28', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         (~ (v1_relat_1 @ X0)
% 1.65/1.88          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 1.65/1.88      inference('sup-', [status(thm)], ['22', '27'])).
% 1.65/1.88  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['23', '24'])).
% 1.65/1.88  thf(t62_relat_1, conjecture,
% 1.65/1.88    (![A:$i]:
% 1.65/1.88     ( ( v1_relat_1 @ A ) =>
% 1.65/1.88       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.65/1.88         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 1.65/1.88  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.88    (~( ![A:$i]:
% 1.65/1.88        ( ( v1_relat_1 @ A ) =>
% 1.65/1.88          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.65/1.88            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 1.65/1.88    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 1.65/1.88  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['23', '24'])).
% 1.65/1.88  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['23', '24'])).
% 1.65/1.88  thf(t41_relat_1, axiom,
% 1.65/1.88    (![A:$i]:
% 1.65/1.88     ( ( v1_relat_1 @ A ) =>
% 1.65/1.88       ( ![B:$i]:
% 1.65/1.88         ( ( v1_relat_1 @ B ) =>
% 1.65/1.88           ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) ) =
% 1.65/1.88             ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) ))).
% 1.65/1.88  thf('33', plain,
% 1.65/1.88      (![X29 : $i, X30 : $i]:
% 1.65/1.88         (~ (v1_relat_1 @ X29)
% 1.65/1.88          | ((k4_relat_1 @ (k6_subset_1 @ X30 @ X29))
% 1.65/1.88              = (k6_subset_1 @ (k4_relat_1 @ X30) @ (k4_relat_1 @ X29)))
% 1.65/1.88          | ~ (v1_relat_1 @ X30))),
% 1.65/1.88      inference('cnf', [status(esa)], [t41_relat_1])).
% 1.65/1.88  thf(redefinition_k6_subset_1, axiom,
% 1.65/1.88    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.65/1.88  thf('34', plain,
% 1.65/1.88      (![X21 : $i, X22 : $i]:
% 1.65/1.88         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 1.65/1.88      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.65/1.88  thf('35', plain,
% 1.65/1.88      (![X21 : $i, X22 : $i]:
% 1.65/1.88         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 1.65/1.88      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.65/1.88  thf('36', plain,
% 1.65/1.88      (![X29 : $i, X30 : $i]:
% 1.65/1.88         (~ (v1_relat_1 @ X29)
% 1.65/1.88          | ((k4_relat_1 @ (k4_xboole_0 @ X30 @ X29))
% 1.65/1.88              = (k4_xboole_0 @ (k4_relat_1 @ X30) @ (k4_relat_1 @ X29)))
% 1.65/1.88          | ~ (v1_relat_1 @ X30))),
% 1.65/1.88      inference('demod', [status(thm)], ['33', '34', '35'])).
% 1.65/1.88  thf('37', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))
% 1.65/1.88          | ~ (v1_relat_1 @ X0)
% 1.65/1.88          | ~ (v1_relat_1 @ X0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['32', '36'])).
% 1.65/1.88  thf('38', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (v1_relat_1 @ X0)
% 1.65/1.88          | ((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0)))),
% 1.65/1.88      inference('simplify', [status(thm)], ['37'])).
% 1.65/1.88  thf('39', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['31', '38'])).
% 1.65/1.88  thf('40', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.88      inference('sup-', [status(thm)], ['30', '39'])).
% 1.65/1.88  thf('41', plain,
% 1.65/1.88      (![X0 : $i]: ((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['29', '40'])).
% 1.65/1.88  thf('42', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 1.65/1.88          | ~ (v1_relat_1 @ X0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['28', '41'])).
% 1.65/1.88  thf('43', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         (((k4_relat_1 @ (k5_relat_1 @ X0 @ X1)) = (k1_xboole_0))
% 1.65/1.88          | ~ (v1_xboole_0 @ X0)
% 1.65/1.88          | ~ (v1_relat_1 @ X1))),
% 1.65/1.88      inference('sup+', [status(thm)], ['1', '42'])).
% 1.65/1.88  thf('44', plain,
% 1.65/1.88      (![X0 : $i]: ((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['29', '40'])).
% 1.65/1.88  thf(t54_relat_1, axiom,
% 1.65/1.88    (![A:$i]:
% 1.65/1.88     ( ( v1_relat_1 @ A ) =>
% 1.65/1.88       ( ![B:$i]:
% 1.65/1.88         ( ( v1_relat_1 @ B ) =>
% 1.65/1.88           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.65/1.88             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 1.65/1.88  thf('45', plain,
% 1.65/1.88      (![X33 : $i, X34 : $i]:
% 1.65/1.88         (~ (v1_relat_1 @ X33)
% 1.65/1.88          | ((k4_relat_1 @ (k5_relat_1 @ X34 @ X33))
% 1.65/1.88              = (k5_relat_1 @ (k4_relat_1 @ X33) @ (k4_relat_1 @ X34)))
% 1.65/1.88          | ~ (v1_relat_1 @ X34))),
% 1.65/1.88      inference('cnf', [status(esa)], [t54_relat_1])).
% 1.65/1.88  thf('46', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         (((k4_relat_1 @ (k5_relat_1 @ (k4_xboole_0 @ X0 @ X0) @ X1))
% 1.65/1.88            = (k5_relat_1 @ (k4_relat_1 @ X1) @ k1_xboole_0))
% 1.65/1.88          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X0))
% 1.65/1.88          | ~ (v1_relat_1 @ X1))),
% 1.65/1.88      inference('sup+', [status(thm)], ['44', '45'])).
% 1.65/1.88  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['23', '24'])).
% 1.65/1.88  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['23', '24'])).
% 1.65/1.88  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.88  thf('50', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['48', '49'])).
% 1.65/1.88  thf('51', plain, (![X23 : $i]: ((v1_relat_1 @ X23) | ~ (v1_xboole_0 @ X23))),
% 1.65/1.88      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.65/1.88  thf('52', plain, (![X23 : $i]: ((v1_relat_1 @ X23) | ~ (v1_xboole_0 @ X23))),
% 1.65/1.88      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.65/1.88  thf('53', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (v1_relat_1 @ X0)
% 1.65/1.88          | ((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0)))),
% 1.65/1.88      inference('simplify', [status(thm)], ['37'])).
% 1.65/1.88  thf(dt_k4_relat_1, axiom,
% 1.65/1.88    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 1.65/1.88  thf('54', plain,
% 1.65/1.88      (![X24 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X24)) | ~ (v1_relat_1 @ X24))),
% 1.65/1.88      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.65/1.88  thf('55', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         ((v1_relat_1 @ k1_xboole_0)
% 1.65/1.88          | ~ (v1_relat_1 @ X0)
% 1.65/1.88          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.65/1.88      inference('sup+', [status(thm)], ['53', '54'])).
% 1.65/1.88  thf('56', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))
% 1.65/1.88          | ~ (v1_relat_1 @ X0)
% 1.65/1.88          | (v1_relat_1 @ k1_xboole_0))),
% 1.65/1.88      inference('sup-', [status(thm)], ['52', '55'])).
% 1.65/1.88  thf('57', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['48', '49'])).
% 1.65/1.88  thf('58', plain,
% 1.65/1.88      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 1.65/1.88      inference('demod', [status(thm)], ['56', '57'])).
% 1.65/1.88  thf('59', plain,
% 1.65/1.88      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 1.65/1.88      inference('sup-', [status(thm)], ['51', '58'])).
% 1.65/1.88  thf('60', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.65/1.88      inference('sup-', [status(thm)], ['50', '59'])).
% 1.65/1.88  thf('61', plain, (![X0 : $i]: (v1_relat_1 @ (k4_xboole_0 @ X0 @ X0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['47', '60'])).
% 1.65/1.88  thf('62', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         (((k4_relat_1 @ (k5_relat_1 @ (k4_xboole_0 @ X0 @ X0) @ X1))
% 1.65/1.88            = (k5_relat_1 @ (k4_relat_1 @ X1) @ k1_xboole_0))
% 1.65/1.88          | ~ (v1_relat_1 @ X1))),
% 1.65/1.88      inference('demod', [status(thm)], ['46', '61'])).
% 1.65/1.88  thf('63', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         (((k1_xboole_0) = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0))
% 1.65/1.88          | ~ (v1_relat_1 @ X0)
% 1.65/1.88          | ~ (v1_xboole_0 @ (k4_xboole_0 @ X1 @ X1))
% 1.65/1.88          | ~ (v1_relat_1 @ X0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['43', '62'])).
% 1.65/1.88  thf('64', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['48', '49'])).
% 1.65/1.88  thf('65', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (((k1_xboole_0) = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0))
% 1.65/1.88          | ~ (v1_relat_1 @ X0)
% 1.65/1.88          | ~ (v1_relat_1 @ X0))),
% 1.65/1.88      inference('demod', [status(thm)], ['63', '64'])).
% 1.65/1.88  thf('66', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (v1_relat_1 @ X0)
% 1.65/1.88          | ((k1_xboole_0) = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0)))),
% 1.65/1.88      inference('simplify', [status(thm)], ['65'])).
% 1.65/1.88  thf('67', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.65/1.88          | ~ (v1_relat_1 @ X0)
% 1.65/1.88          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 1.65/1.88      inference('sup+', [status(thm)], ['0', '66'])).
% 1.65/1.88  thf('68', plain,
% 1.65/1.88      (![X24 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X24)) | ~ (v1_relat_1 @ X24))),
% 1.65/1.88      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.65/1.88  thf('69', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (v1_relat_1 @ X0)
% 1.65/1.88          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.65/1.88      inference('clc', [status(thm)], ['67', '68'])).
% 1.65/1.88  thf('70', plain,
% 1.65/1.88      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.65/1.88  thf('71', plain,
% 1.65/1.88      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 1.65/1.88        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('72', plain,
% 1.65/1.88      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 1.65/1.88         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.65/1.88      inference('split', [status(esa)], ['71'])).
% 1.65/1.88  thf('73', plain,
% 1.65/1.88      ((![X0 : $i]:
% 1.65/1.88          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 1.65/1.88         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.65/1.88      inference('sup-', [status(thm)], ['70', '72'])).
% 1.65/1.88  thf('74', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.65/1.88      inference('demod', [status(thm)], ['20', '21'])).
% 1.65/1.88  thf('75', plain,
% 1.65/1.88      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.65/1.88  thf('76', plain,
% 1.65/1.88      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.65/1.88  thf('77', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.88      inference('sup+', [status(thm)], ['75', '76'])).
% 1.65/1.88  thf('78', plain,
% 1.65/1.88      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 1.65/1.88         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.65/1.88      inference('split', [status(esa)], ['71'])).
% 1.65/1.88  thf('79', plain,
% 1.65/1.88      ((![X0 : $i]:
% 1.65/1.88          (((X0) != (k1_xboole_0))
% 1.65/1.88           | ~ (v1_xboole_0 @ X0)
% 1.65/1.88           | ~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A))))
% 1.65/1.88         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.65/1.88      inference('sup-', [status(thm)], ['77', '78'])).
% 1.65/1.88  thf('80', plain,
% 1.65/1.88      (((~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A))
% 1.65/1.88         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.65/1.88         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.65/1.88      inference('simplify', [status(thm)], ['79'])).
% 1.65/1.88  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.88  thf('82', plain,
% 1.65/1.88      ((~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A)))
% 1.65/1.88         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.65/1.88      inference('simplify_reflect+', [status(thm)], ['80', '81'])).
% 1.65/1.88  thf('83', plain,
% 1.65/1.88      ((~ (v1_relat_1 @ sk_A))
% 1.65/1.88         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.65/1.88      inference('sup-', [status(thm)], ['74', '82'])).
% 1.65/1.88  thf('84', plain, ((v1_relat_1 @ sk_A)),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('85', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.65/1.88      inference('demod', [status(thm)], ['83', '84'])).
% 1.65/1.88  thf('86', plain,
% 1.65/1.88      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 1.65/1.88       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.65/1.88      inference('split', [status(esa)], ['71'])).
% 1.65/1.88  thf('87', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 1.65/1.88      inference('sat_resolution*', [status(thm)], ['85', '86'])).
% 1.65/1.88  thf('88', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.88      inference('simpl_trail', [status(thm)], ['73', '87'])).
% 1.65/1.88  thf('89', plain,
% 1.65/1.88      ((((k1_xboole_0) != (k1_xboole_0))
% 1.65/1.88        | ~ (v1_relat_1 @ sk_A)
% 1.65/1.88        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.65/1.88      inference('sup-', [status(thm)], ['69', '88'])).
% 1.65/1.88  thf('90', plain, ((v1_relat_1 @ sk_A)),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.88  thf('92', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.65/1.88      inference('demod', [status(thm)], ['89', '90', '91'])).
% 1.65/1.88  thf('93', plain, ($false), inference('simplify', [status(thm)], ['92'])).
% 1.65/1.88  
% 1.65/1.88  % SZS output end Refutation
% 1.65/1.88  
% 1.65/1.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
