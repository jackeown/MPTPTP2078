%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2VRe8feqvl

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:27 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 292 expanded)
%              Number of leaves         :   28 ( 101 expanded)
%              Depth                    :   24
%              Number of atoms          :  672 (1908 expanded)
%              Number of equality atoms :   54 ( 135 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X27 @ X25 @ X26 ) @ ( sk_E @ X27 @ X25 @ X26 ) ) @ X27 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X27 @ X25 @ X26 ) @ ( sk_F @ X27 @ X25 @ X26 ) ) @ X26 )
      | ( X27
        = ( k5_relat_1 @ X26 @ X25 ) )
      | ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ( ( k4_xboole_0 @ X22 @ ( k1_tarski @ X21 ) )
       != X22 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_F @ X0 @ X2 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

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

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('11',plain,(
    ! [X24: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_relat_1 @ X34 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('13',plain,(
    ! [X24: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('15',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X37 @ X36 ) ) @ ( k2_relat_1 @ X36 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('20',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X35: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X35 ) )
      | ~ ( v1_relat_1 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['11','29'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_relat_1 @ X34 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    ! [X24: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','44'])).

thf('46',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('49',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('57',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('68',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_A )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['51','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','45'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect+',[status(thm)],['74','75','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2VRe8feqvl
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:18:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.03/2.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.03/2.23  % Solved by: fo/fo7.sh
% 2.03/2.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.03/2.23  % done 2147 iterations in 1.784s
% 2.03/2.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.03/2.23  % SZS output start Refutation
% 2.03/2.23  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 2.03/2.23  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.03/2.23  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.03/2.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.03/2.23  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.03/2.23  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.03/2.23  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.03/2.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.03/2.23  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.03/2.23  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.03/2.23  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 2.03/2.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.03/2.23  thf(sk_A_type, type, sk_A: $i).
% 2.03/2.23  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.03/2.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.03/2.23  thf(d8_relat_1, axiom,
% 2.03/2.23    (![A:$i]:
% 2.03/2.23     ( ( v1_relat_1 @ A ) =>
% 2.03/2.23       ( ![B:$i]:
% 2.03/2.23         ( ( v1_relat_1 @ B ) =>
% 2.03/2.23           ( ![C:$i]:
% 2.03/2.23             ( ( v1_relat_1 @ C ) =>
% 2.03/2.23               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 2.03/2.23                 ( ![D:$i,E:$i]:
% 2.03/2.23                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 2.03/2.23                     ( ?[F:$i]:
% 2.03/2.23                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 2.03/2.23                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 2.03/2.23  thf('0', plain,
% 2.03/2.23      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.03/2.23         (~ (v1_relat_1 @ X25)
% 2.03/2.23          | (r2_hidden @ 
% 2.03/2.23             (k4_tarski @ (sk_D @ X27 @ X25 @ X26) @ (sk_E @ X27 @ X25 @ X26)) @ 
% 2.03/2.23             X27)
% 2.03/2.23          | (r2_hidden @ 
% 2.03/2.23             (k4_tarski @ (sk_D @ X27 @ X25 @ X26) @ (sk_F @ X27 @ X25 @ X26)) @ 
% 2.03/2.23             X26)
% 2.03/2.23          | ((X27) = (k5_relat_1 @ X26 @ X25))
% 2.03/2.23          | ~ (v1_relat_1 @ X27)
% 2.03/2.23          | ~ (v1_relat_1 @ X26))),
% 2.03/2.23      inference('cnf', [status(esa)], [d8_relat_1])).
% 2.03/2.23  thf(l13_xboole_0, axiom,
% 2.03/2.23    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.03/2.23  thf('1', plain,
% 2.03/2.23      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.03/2.23      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.03/2.23  thf(t4_boole, axiom,
% 2.03/2.23    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 2.03/2.23  thf('2', plain,
% 2.03/2.23      (![X5 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.03/2.23      inference('cnf', [status(esa)], [t4_boole])).
% 2.03/2.23  thf(t65_zfmisc_1, axiom,
% 2.03/2.23    (![A:$i,B:$i]:
% 2.03/2.23     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.03/2.23       ( ~( r2_hidden @ B @ A ) ) ))).
% 2.03/2.23  thf('3', plain,
% 2.03/2.23      (![X21 : $i, X22 : $i]:
% 2.03/2.23         (~ (r2_hidden @ X21 @ X22)
% 2.03/2.23          | ((k4_xboole_0 @ X22 @ (k1_tarski @ X21)) != (X22)))),
% 2.03/2.23      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.03/2.23  thf('4', plain,
% 2.03/2.23      (![X0 : $i]:
% 2.03/2.23         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 2.03/2.23      inference('sup-', [status(thm)], ['2', '3'])).
% 2.03/2.23  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.03/2.23      inference('simplify', [status(thm)], ['4'])).
% 2.03/2.23  thf('6', plain,
% 2.03/2.23      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.03/2.23      inference('sup-', [status(thm)], ['1', '5'])).
% 2.03/2.23  thf('7', plain,
% 2.03/2.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.03/2.23         (~ (v1_relat_1 @ X1)
% 2.03/2.23          | ~ (v1_relat_1 @ X0)
% 2.03/2.23          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 2.03/2.23          | (r2_hidden @ 
% 2.03/2.23             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_F @ X0 @ X2 @ X1)) @ X1)
% 2.03/2.23          | ~ (v1_relat_1 @ X2)
% 2.03/2.23          | ~ (v1_xboole_0 @ X0))),
% 2.03/2.23      inference('sup-', [status(thm)], ['0', '6'])).
% 2.03/2.23  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.03/2.23      inference('simplify', [status(thm)], ['4'])).
% 2.03/2.23  thf('9', plain,
% 2.03/2.23      (![X0 : $i, X1 : $i]:
% 2.03/2.23         (~ (v1_xboole_0 @ X1)
% 2.03/2.23          | ~ (v1_relat_1 @ X0)
% 2.03/2.23          | ((X1) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 2.03/2.23          | ~ (v1_relat_1 @ X1)
% 2.03/2.23          | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.03/2.23      inference('sup-', [status(thm)], ['7', '8'])).
% 2.03/2.23  thf(t62_relat_1, conjecture,
% 2.03/2.23    (![A:$i]:
% 2.03/2.23     ( ( v1_relat_1 @ A ) =>
% 2.03/2.23       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 2.03/2.23         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 2.03/2.23  thf(zf_stmt_0, negated_conjecture,
% 2.03/2.23    (~( ![A:$i]:
% 2.03/2.23        ( ( v1_relat_1 @ A ) =>
% 2.03/2.23          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 2.03/2.23            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 2.03/2.23    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 2.03/2.23  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf(cc1_relat_1, axiom,
% 2.03/2.23    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 2.03/2.23  thf('11', plain, (![X24 : $i]: ((v1_relat_1 @ X24) | ~ (v1_xboole_0 @ X24))),
% 2.03/2.23      inference('cnf', [status(esa)], [cc1_relat_1])).
% 2.03/2.23  thf(dt_k5_relat_1, axiom,
% 2.03/2.23    (![A:$i,B:$i]:
% 2.03/2.23     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 2.03/2.23       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 2.03/2.23  thf('12', plain,
% 2.03/2.23      (![X33 : $i, X34 : $i]:
% 2.03/2.23         (~ (v1_relat_1 @ X33)
% 2.03/2.23          | ~ (v1_relat_1 @ X34)
% 2.03/2.23          | (v1_relat_1 @ (k5_relat_1 @ X33 @ X34)))),
% 2.03/2.23      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.03/2.23  thf('13', plain, (![X24 : $i]: ((v1_relat_1 @ X24) | ~ (v1_xboole_0 @ X24))),
% 2.03/2.23      inference('cnf', [status(esa)], [cc1_relat_1])).
% 2.03/2.23  thf(t60_relat_1, axiom,
% 2.03/2.23    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 2.03/2.23     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.03/2.23  thf('14', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.03/2.23      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.03/2.23  thf(t45_relat_1, axiom,
% 2.03/2.23    (![A:$i]:
% 2.03/2.23     ( ( v1_relat_1 @ A ) =>
% 2.03/2.23       ( ![B:$i]:
% 2.03/2.23         ( ( v1_relat_1 @ B ) =>
% 2.03/2.23           ( r1_tarski @
% 2.03/2.23             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 2.03/2.23  thf('15', plain,
% 2.03/2.23      (![X36 : $i, X37 : $i]:
% 2.03/2.23         (~ (v1_relat_1 @ X36)
% 2.03/2.23          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X37 @ X36)) @ 
% 2.03/2.23             (k2_relat_1 @ X36))
% 2.03/2.23          | ~ (v1_relat_1 @ X37))),
% 2.03/2.23      inference('cnf', [status(esa)], [t45_relat_1])).
% 2.03/2.23  thf('16', plain,
% 2.03/2.23      (![X0 : $i]:
% 2.03/2.23         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 2.03/2.23           k1_xboole_0)
% 2.03/2.23          | ~ (v1_relat_1 @ X0)
% 2.03/2.24          | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.03/2.24      inference('sup+', [status(thm)], ['14', '15'])).
% 2.03/2.24  thf('17', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.03/2.24          | ~ (v1_relat_1 @ X0)
% 2.03/2.24          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 2.03/2.24             k1_xboole_0))),
% 2.03/2.24      inference('sup-', [status(thm)], ['13', '16'])).
% 2.03/2.24  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.03/2.24  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.03/2.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.03/2.24  thf('19', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X0)
% 2.03/2.24          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 2.03/2.24             k1_xboole_0))),
% 2.03/2.24      inference('demod', [status(thm)], ['17', '18'])).
% 2.03/2.24  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.03/2.24  thf('20', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 2.03/2.24      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.03/2.24  thf(d10_xboole_0, axiom,
% 2.03/2.24    (![A:$i,B:$i]:
% 2.03/2.24     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.03/2.24  thf('21', plain,
% 2.03/2.24      (![X1 : $i, X3 : $i]:
% 2.03/2.24         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 2.03/2.24      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.03/2.24  thf('22', plain,
% 2.03/2.24      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.03/2.24      inference('sup-', [status(thm)], ['20', '21'])).
% 2.03/2.24  thf('23', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X0)
% 2.03/2.24          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 2.03/2.24      inference('sup-', [status(thm)], ['19', '22'])).
% 2.03/2.24  thf(fc9_relat_1, axiom,
% 2.03/2.24    (![A:$i]:
% 2.03/2.24     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 2.03/2.24       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 2.03/2.24  thf('24', plain,
% 2.03/2.24      (![X35 : $i]:
% 2.03/2.24         (~ (v1_xboole_0 @ (k2_relat_1 @ X35))
% 2.03/2.24          | ~ (v1_relat_1 @ X35)
% 2.03/2.24          | (v1_xboole_0 @ X35))),
% 2.03/2.24      inference('cnf', [status(esa)], [fc9_relat_1])).
% 2.03/2.24  thf('25', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.03/2.24          | ~ (v1_relat_1 @ X0)
% 2.03/2.24          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 2.03/2.24          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 2.03/2.24      inference('sup-', [status(thm)], ['23', '24'])).
% 2.03/2.24  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.03/2.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.03/2.24  thf('27', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X0)
% 2.03/2.24          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 2.03/2.24          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 2.03/2.24      inference('demod', [status(thm)], ['25', '26'])).
% 2.03/2.24  thf('28', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ k1_xboole_0)
% 2.03/2.24          | ~ (v1_relat_1 @ X0)
% 2.03/2.24          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 2.03/2.24          | ~ (v1_relat_1 @ X0))),
% 2.03/2.24      inference('sup-', [status(thm)], ['12', '27'])).
% 2.03/2.24  thf('29', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 2.03/2.24          | ~ (v1_relat_1 @ X0)
% 2.03/2.24          | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.03/2.24      inference('simplify', [status(thm)], ['28'])).
% 2.03/2.24  thf('30', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.03/2.24          | ~ (v1_relat_1 @ X0)
% 2.03/2.24          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 2.03/2.24      inference('sup-', [status(thm)], ['11', '29'])).
% 2.03/2.24  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.03/2.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.03/2.24  thf('32', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 2.03/2.24      inference('demod', [status(thm)], ['30', '31'])).
% 2.03/2.24  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('34', plain,
% 2.03/2.24      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.03/2.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.03/2.24  thf('35', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 2.03/2.24      inference('demod', [status(thm)], ['30', '31'])).
% 2.03/2.24  thf('36', plain,
% 2.03/2.24      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.03/2.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.03/2.24  thf('37', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X0)
% 2.03/2.24          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 2.03/2.24      inference('sup-', [status(thm)], ['35', '36'])).
% 2.03/2.24  thf('38', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         (((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 2.03/2.24          | ~ (v1_xboole_0 @ X0)
% 2.03/2.24          | ~ (v1_relat_1 @ X1))),
% 2.03/2.24      inference('sup+', [status(thm)], ['34', '37'])).
% 2.03/2.24  thf('39', plain,
% 2.03/2.24      (![X33 : $i, X34 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X33)
% 2.03/2.24          | ~ (v1_relat_1 @ X34)
% 2.03/2.24          | (v1_relat_1 @ (k5_relat_1 @ X33 @ X34)))),
% 2.03/2.24      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.03/2.24  thf('40', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         ((v1_relat_1 @ k1_xboole_0)
% 2.03/2.24          | ~ (v1_relat_1 @ X1)
% 2.03/2.24          | ~ (v1_xboole_0 @ X0)
% 2.03/2.24          | ~ (v1_relat_1 @ X0)
% 2.03/2.24          | ~ (v1_relat_1 @ X1))),
% 2.03/2.24      inference('sup+', [status(thm)], ['38', '39'])).
% 2.03/2.24  thf('41', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X0)
% 2.03/2.24          | ~ (v1_xboole_0 @ X0)
% 2.03/2.24          | ~ (v1_relat_1 @ X1)
% 2.03/2.24          | (v1_relat_1 @ k1_xboole_0))),
% 2.03/2.24      inference('simplify', [status(thm)], ['40'])).
% 2.03/2.24  thf('42', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         ((v1_relat_1 @ k1_xboole_0)
% 2.03/2.24          | ~ (v1_xboole_0 @ X0)
% 2.03/2.24          | ~ (v1_relat_1 @ X0))),
% 2.03/2.24      inference('sup-', [status(thm)], ['33', '41'])).
% 2.03/2.24  thf('43', plain, (![X24 : $i]: ((v1_relat_1 @ X24) | ~ (v1_xboole_0 @ X24))),
% 2.03/2.24      inference('cnf', [status(esa)], [cc1_relat_1])).
% 2.03/2.24  thf('44', plain,
% 2.03/2.24      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 2.03/2.24      inference('clc', [status(thm)], ['42', '43'])).
% 2.03/2.24  thf('45', plain,
% 2.03/2.24      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 2.03/2.24      inference('sup-', [status(thm)], ['32', '44'])).
% 2.03/2.24  thf('46', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.03/2.24      inference('sup-', [status(thm)], ['10', '45'])).
% 2.03/2.24  thf('47', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         (~ (v1_xboole_0 @ X1)
% 2.03/2.24          | ~ (v1_relat_1 @ X0)
% 2.03/2.24          | ((X1) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 2.03/2.24          | ~ (v1_relat_1 @ X1))),
% 2.03/2.24      inference('demod', [status(thm)], ['9', '46'])).
% 2.03/2.24  thf('48', plain,
% 2.03/2.24      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.03/2.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.03/2.24  thf('49', plain,
% 2.03/2.24      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 2.03/2.24        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('50', plain,
% 2.03/2.24      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 2.03/2.24         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 2.03/2.24      inference('split', [status(esa)], ['49'])).
% 2.03/2.24  thf('51', plain,
% 2.03/2.24      ((![X0 : $i]:
% 2.03/2.24          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 2.03/2.24         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 2.03/2.24      inference('sup-', [status(thm)], ['48', '50'])).
% 2.03/2.24  thf('52', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 2.03/2.24      inference('demod', [status(thm)], ['30', '31'])).
% 2.03/2.24  thf('53', plain,
% 2.03/2.24      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.03/2.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.03/2.24  thf('54', plain,
% 2.03/2.24      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.03/2.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.03/2.24  thf('55', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 2.03/2.24      inference('sup+', [status(thm)], ['53', '54'])).
% 2.03/2.24  thf('56', plain,
% 2.03/2.24      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.03/2.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.03/2.24  thf('57', plain,
% 2.03/2.24      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 2.03/2.24         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 2.03/2.24      inference('split', [status(esa)], ['49'])).
% 2.03/2.24  thf('58', plain,
% 2.03/2.24      ((![X0 : $i]:
% 2.03/2.24          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 2.03/2.24         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 2.03/2.24      inference('sup-', [status(thm)], ['56', '57'])).
% 2.03/2.24  thf('59', plain,
% 2.03/2.24      ((![X0 : $i, X1 : $i]:
% 2.03/2.24          (((X0) != (k1_xboole_0))
% 2.03/2.24           | ~ (v1_xboole_0 @ X0)
% 2.03/2.24           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 2.03/2.24           | ~ (v1_xboole_0 @ X1)))
% 2.03/2.24         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 2.03/2.24      inference('sup-', [status(thm)], ['55', '58'])).
% 2.03/2.24  thf('60', plain,
% 2.03/2.24      ((![X1 : $i]:
% 2.03/2.24          (~ (v1_xboole_0 @ X1)
% 2.03/2.24           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 2.03/2.24           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 2.03/2.24         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 2.03/2.24      inference('simplify', [status(thm)], ['59'])).
% 2.03/2.24  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.03/2.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.03/2.24  thf('62', plain,
% 2.03/2.24      ((![X1 : $i]:
% 2.03/2.24          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))))
% 2.03/2.24         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 2.03/2.24      inference('simplify_reflect+', [status(thm)], ['60', '61'])).
% 2.03/2.24  thf('63', plain,
% 2.03/2.24      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 2.03/2.24         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 2.03/2.24      inference('sup-', [status(thm)], ['52', '62'])).
% 2.03/2.24  thf('64', plain, ((v1_relat_1 @ sk_A)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.03/2.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.03/2.24  thf('66', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 2.03/2.24      inference('demod', [status(thm)], ['63', '64', '65'])).
% 2.03/2.24  thf('67', plain,
% 2.03/2.24      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 2.03/2.24       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 2.03/2.24      inference('split', [status(esa)], ['49'])).
% 2.03/2.24  thf('68', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 2.03/2.24      inference('sat_resolution*', [status(thm)], ['66', '67'])).
% 2.03/2.24  thf('69', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.03/2.24      inference('simpl_trail', [status(thm)], ['51', '68'])).
% 2.03/2.24  thf('70', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (((X0) != (k1_xboole_0))
% 2.03/2.24          | ~ (v1_relat_1 @ X0)
% 2.03/2.24          | ~ (v1_relat_1 @ sk_A)
% 2.03/2.24          | ~ (v1_xboole_0 @ X0)
% 2.03/2.24          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 2.03/2.24      inference('sup-', [status(thm)], ['47', '69'])).
% 2.03/2.24  thf('71', plain, ((v1_relat_1 @ sk_A)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.03/2.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.03/2.24  thf('73', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (((X0) != (k1_xboole_0)) | ~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['70', '71', '72'])).
% 2.03/2.24  thf('74', plain,
% 2.03/2.24      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.03/2.24      inference('simplify', [status(thm)], ['73'])).
% 2.03/2.24  thf('75', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.03/2.24      inference('sup-', [status(thm)], ['10', '45'])).
% 2.03/2.24  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.03/2.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.03/2.24  thf('77', plain, ($false),
% 2.03/2.24      inference('simplify_reflect+', [status(thm)], ['74', '75', '76'])).
% 2.03/2.24  
% 2.03/2.24  % SZS output end Refutation
% 2.03/2.24  
% 2.03/2.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
