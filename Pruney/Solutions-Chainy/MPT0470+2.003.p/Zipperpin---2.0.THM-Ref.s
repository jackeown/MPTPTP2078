%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UNPqqPtYSH

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:26 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 261 expanded)
%              Number of leaves         :   23 (  89 expanded)
%              Depth                    :   30
%              Number of atoms          :  752 (1703 expanded)
%              Number of equality atoms :   55 ( 128 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,
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

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X19 @ X18 ) )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('13',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('17',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('18',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['15','35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','40'])).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('55',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','58'])).

thf('60',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','49'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('64',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('67',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('76',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['67'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('80',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['67'])).

thf('85',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['73','85'])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['87','88','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UNPqqPtYSH
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.56/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.56/0.74  % Solved by: fo/fo7.sh
% 0.56/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.74  % done 537 iterations in 0.288s
% 0.56/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.56/0.74  % SZS output start Refutation
% 0.56/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.56/0.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.56/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.56/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.56/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.74  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.56/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.56/0.74  thf(dt_k5_relat_1, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.56/0.74       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.56/0.74  thf('0', plain,
% 0.56/0.74      (![X12 : $i, X13 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X12)
% 0.56/0.74          | ~ (v1_relat_1 @ X13)
% 0.56/0.74          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.56/0.74  thf(d3_tarski, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( r1_tarski @ A @ B ) <=>
% 0.56/0.74       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.56/0.74  thf('1', plain,
% 0.56/0.74      (![X4 : $i, X6 : $i]:
% 0.56/0.74         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.56/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.56/0.74  thf(d1_xboole_0, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.56/0.74  thf('2', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.74  thf('3', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.56/0.74  thf(t60_relat_1, axiom,
% 0.56/0.74    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.56/0.74     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.56/0.74  thf('4', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.74      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.56/0.74  thf(t46_relat_1, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( v1_relat_1 @ A ) =>
% 0.56/0.74       ( ![B:$i]:
% 0.56/0.74         ( ( v1_relat_1 @ B ) =>
% 0.56/0.74           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.56/0.74             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.56/0.74  thf('5', plain,
% 0.56/0.74      (![X18 : $i, X19 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X18)
% 0.56/0.74          | ((k1_relat_1 @ (k5_relat_1 @ X19 @ X18)) = (k1_relat_1 @ X19))
% 0.56/0.74          | ~ (r1_tarski @ (k2_relat_1 @ X19) @ (k1_relat_1 @ X18))
% 0.56/0.74          | ~ (v1_relat_1 @ X19))),
% 0.56/0.74      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.56/0.74  thf('6', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.56/0.74          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.56/0.74          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.56/0.74              = (k1_relat_1 @ k1_xboole_0))
% 0.56/0.74          | ~ (v1_relat_1 @ X0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['4', '5'])).
% 0.56/0.74  thf('7', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.74      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.56/0.74  thf('8', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.56/0.74          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.56/0.74          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.56/0.74          | ~ (v1_relat_1 @ X0))),
% 0.56/0.74      inference('demod', [status(thm)], ['6', '7'])).
% 0.56/0.74  thf(t62_relat_1, conjecture,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( v1_relat_1 @ A ) =>
% 0.56/0.74       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.56/0.74         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.56/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.74    (~( ![A:$i]:
% 0.56/0.74        ( ( v1_relat_1 @ A ) =>
% 0.56/0.74          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.56/0.74            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.56/0.74    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.56/0.74  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('10', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.74      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.56/0.74  thf(cc1_relat_1, axiom,
% 0.56/0.74    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.56/0.74  thf('11', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.56/0.74      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.56/0.74  thf(l13_xboole_0, axiom,
% 0.56/0.74    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.56/0.74  thf('12', plain,
% 0.56/0.74      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.56/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.56/0.74  thf('13', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.74      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.56/0.74  thf('14', plain,
% 0.56/0.74      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['12', '13'])).
% 0.56/0.74  thf('15', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.56/0.74      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.56/0.74  thf('16', plain,
% 0.56/0.74      (![X12 : $i, X13 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X12)
% 0.56/0.74          | ~ (v1_relat_1 @ X13)
% 0.56/0.74          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.56/0.74  thf('17', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.56/0.74      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.56/0.74  thf('18', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.74      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.56/0.74  thf(t45_relat_1, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( v1_relat_1 @ A ) =>
% 0.56/0.74       ( ![B:$i]:
% 0.56/0.74         ( ( v1_relat_1 @ B ) =>
% 0.56/0.74           ( r1_tarski @
% 0.56/0.74             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.56/0.74  thf('19', plain,
% 0.56/0.74      (![X16 : $i, X17 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X16)
% 0.56/0.74          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X17 @ X16)) @ 
% 0.56/0.74             (k2_relat_1 @ X16))
% 0.56/0.74          | ~ (v1_relat_1 @ X17))),
% 0.56/0.74      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.56/0.74  thf('20', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.56/0.74           k1_xboole_0)
% 0.56/0.74          | ~ (v1_relat_1 @ X0)
% 0.56/0.74          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['18', '19'])).
% 0.56/0.74  thf('21', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.56/0.74          | ~ (v1_relat_1 @ X0)
% 0.56/0.74          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.56/0.74             k1_xboole_0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['17', '20'])).
% 0.56/0.74  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.56/0.74  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.74  thf('23', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X0)
% 0.56/0.74          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.56/0.74             k1_xboole_0))),
% 0.56/0.74      inference('demod', [status(thm)], ['21', '22'])).
% 0.56/0.74  thf('24', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.56/0.74  thf(d10_xboole_0, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.56/0.74  thf('25', plain,
% 0.56/0.74      (![X8 : $i, X10 : $i]:
% 0.56/0.74         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.56/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.56/0.74  thf('26', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['24', '25'])).
% 0.56/0.74  thf('27', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X0)
% 0.56/0.74          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.56/0.74          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['23', '26'])).
% 0.56/0.74  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.74  thf('29', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X0)
% 0.56/0.74          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.56/0.74      inference('demod', [status(thm)], ['27', '28'])).
% 0.56/0.74  thf(fc9_relat_1, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.56/0.74       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.56/0.74  thf('30', plain,
% 0.56/0.74      (![X15 : $i]:
% 0.56/0.74         (~ (v1_xboole_0 @ (k2_relat_1 @ X15))
% 0.56/0.74          | ~ (v1_relat_1 @ X15)
% 0.56/0.74          | (v1_xboole_0 @ X15))),
% 0.56/0.74      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.56/0.74  thf('31', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.56/0.74          | ~ (v1_relat_1 @ X0)
% 0.56/0.74          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.56/0.74          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['29', '30'])).
% 0.56/0.74  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.74  thf('33', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X0)
% 0.56/0.74          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.56/0.74          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.56/0.74      inference('demod', [status(thm)], ['31', '32'])).
% 0.56/0.74  thf('34', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ k1_xboole_0)
% 0.56/0.74          | ~ (v1_relat_1 @ X0)
% 0.56/0.74          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.56/0.74          | ~ (v1_relat_1 @ X0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['16', '33'])).
% 0.56/0.74  thf('35', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.56/0.74          | ~ (v1_relat_1 @ X0)
% 0.56/0.74          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['34'])).
% 0.56/0.74  thf('36', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.56/0.74          | ~ (v1_relat_1 @ X0)
% 0.56/0.74          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['15', '35'])).
% 0.56/0.74  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.74  thf('38', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.56/0.74      inference('demod', [status(thm)], ['36', '37'])).
% 0.56/0.74  thf('39', plain,
% 0.56/0.74      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.56/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.56/0.74  thf('40', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X0)
% 0.56/0.74          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['38', '39'])).
% 0.56/0.74  thf('41', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         (((k5_relat_1 @ X1 @ (k2_relat_1 @ X0)) = (k1_xboole_0))
% 0.56/0.74          | ~ (v1_xboole_0 @ X0)
% 0.56/0.74          | ~ (v1_relat_1 @ X1))),
% 0.56/0.74      inference('sup+', [status(thm)], ['14', '40'])).
% 0.56/0.74  thf('42', plain,
% 0.56/0.74      (![X12 : $i, X13 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X12)
% 0.56/0.74          | ~ (v1_relat_1 @ X13)
% 0.56/0.74          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.56/0.74  thf('43', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((v1_relat_1 @ k1_xboole_0)
% 0.56/0.74          | ~ (v1_relat_1 @ X1)
% 0.56/0.74          | ~ (v1_xboole_0 @ X0)
% 0.56/0.74          | ~ (v1_relat_1 @ (k2_relat_1 @ X0))
% 0.56/0.74          | ~ (v1_relat_1 @ X1))),
% 0.56/0.74      inference('sup+', [status(thm)], ['41', '42'])).
% 0.56/0.74  thf('44', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ (k2_relat_1 @ X0))
% 0.56/0.74          | ~ (v1_xboole_0 @ X0)
% 0.56/0.74          | ~ (v1_relat_1 @ X1)
% 0.56/0.74          | (v1_relat_1 @ k1_xboole_0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['43'])).
% 0.56/0.74  thf('45', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.56/0.74          | (v1_relat_1 @ k1_xboole_0)
% 0.56/0.74          | ~ (v1_relat_1 @ X1)
% 0.56/0.74          | ~ (v1_xboole_0 @ X0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['11', '44'])).
% 0.56/0.74  thf('46', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.56/0.74          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.56/0.74          | ~ (v1_relat_1 @ X0)
% 0.56/0.74          | (v1_relat_1 @ k1_xboole_0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['10', '45'])).
% 0.56/0.74  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.74  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.74  thf('49', plain,
% 0.56/0.74      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.56/0.74      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.56/0.74  thf('50', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.56/0.74      inference('sup-', [status(thm)], ['9', '49'])).
% 0.56/0.74  thf('51', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.56/0.74          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.56/0.74          | ~ (v1_relat_1 @ X0))),
% 0.56/0.74      inference('demod', [status(thm)], ['8', '50'])).
% 0.56/0.74  thf('52', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.56/0.74          | ~ (v1_relat_1 @ X0)
% 0.56/0.74          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['3', '51'])).
% 0.56/0.74  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.74  thf('54', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X0)
% 0.56/0.74          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.56/0.74      inference('demod', [status(thm)], ['52', '53'])).
% 0.56/0.74  thf(fc8_relat_1, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.56/0.74       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.56/0.74  thf('55', plain,
% 0.56/0.74      (![X14 : $i]:
% 0.56/0.74         (~ (v1_xboole_0 @ (k1_relat_1 @ X14))
% 0.56/0.74          | ~ (v1_relat_1 @ X14)
% 0.56/0.74          | (v1_xboole_0 @ X14))),
% 0.56/0.74      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.56/0.74  thf('56', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.56/0.74          | ~ (v1_relat_1 @ X0)
% 0.56/0.74          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.56/0.74          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['54', '55'])).
% 0.56/0.74  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.74  thf('58', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X0)
% 0.56/0.74          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.56/0.74          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.56/0.74      inference('demod', [status(thm)], ['56', '57'])).
% 0.56/0.74  thf('59', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X0)
% 0.56/0.74          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.56/0.74          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.56/0.74          | ~ (v1_relat_1 @ X0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['0', '58'])).
% 0.56/0.74  thf('60', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.56/0.74      inference('sup-', [status(thm)], ['9', '49'])).
% 0.56/0.74  thf('61', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X0)
% 0.56/0.74          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.56/0.74          | ~ (v1_relat_1 @ X0))),
% 0.56/0.74      inference('demod', [status(thm)], ['59', '60'])).
% 0.56/0.74  thf('62', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['61'])).
% 0.56/0.74  thf('63', plain,
% 0.56/0.74      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.56/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.56/0.74  thf('64', plain,
% 0.56/0.74      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.56/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.56/0.74  thf('65', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.74      inference('sup+', [status(thm)], ['63', '64'])).
% 0.56/0.74  thf('66', plain,
% 0.56/0.74      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.56/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.56/0.74  thf('67', plain,
% 0.56/0.74      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.56/0.74        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('68', plain,
% 0.56/0.74      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.56/0.74         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.56/0.74      inference('split', [status(esa)], ['67'])).
% 0.56/0.74  thf('69', plain,
% 0.56/0.74      ((![X0 : $i]:
% 0.56/0.74          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.56/0.74         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.56/0.74      inference('sup-', [status(thm)], ['66', '68'])).
% 0.56/0.74  thf('70', plain,
% 0.56/0.74      ((![X0 : $i, X1 : $i]:
% 0.56/0.74          (((X0) != (k1_xboole_0))
% 0.56/0.74           | ~ (v1_xboole_0 @ X0)
% 0.56/0.74           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.56/0.74           | ~ (v1_xboole_0 @ X1)))
% 0.56/0.74         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.56/0.74      inference('sup-', [status(thm)], ['65', '69'])).
% 0.56/0.74  thf('71', plain,
% 0.56/0.74      ((![X1 : $i]:
% 0.56/0.74          (~ (v1_xboole_0 @ X1)
% 0.56/0.74           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.56/0.74           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.56/0.74         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.56/0.74      inference('simplify', [status(thm)], ['70'])).
% 0.56/0.74  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.74  thf('73', plain,
% 0.56/0.74      ((![X1 : $i]:
% 0.56/0.74          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.56/0.74         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.56/0.74      inference('simplify_reflect+', [status(thm)], ['71', '72'])).
% 0.56/0.74  thf('74', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.56/0.74      inference('demod', [status(thm)], ['36', '37'])).
% 0.56/0.74  thf('75', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.74      inference('sup+', [status(thm)], ['63', '64'])).
% 0.56/0.74  thf('76', plain,
% 0.56/0.74      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.56/0.74         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.56/0.74      inference('split', [status(esa)], ['67'])).
% 0.56/0.74  thf('77', plain,
% 0.56/0.74      ((![X0 : $i]:
% 0.56/0.74          (((X0) != (k1_xboole_0))
% 0.56/0.74           | ~ (v1_xboole_0 @ X0)
% 0.56/0.74           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 0.56/0.74         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.56/0.74      inference('sup-', [status(thm)], ['75', '76'])).
% 0.56/0.74  thf('78', plain,
% 0.56/0.74      (((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.56/0.74         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.56/0.74         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.56/0.74      inference('simplify', [status(thm)], ['77'])).
% 0.56/0.74  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.74  thf('80', plain,
% 0.56/0.74      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 0.56/0.74         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.56/0.74      inference('simplify_reflect+', [status(thm)], ['78', '79'])).
% 0.56/0.74  thf('81', plain,
% 0.56/0.74      ((~ (v1_relat_1 @ sk_A))
% 0.56/0.74         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.56/0.74      inference('sup-', [status(thm)], ['74', '80'])).
% 0.56/0.74  thf('82', plain, ((v1_relat_1 @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('83', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.56/0.74      inference('demod', [status(thm)], ['81', '82'])).
% 0.56/0.74  thf('84', plain,
% 0.56/0.74      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 0.56/0.74       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.56/0.74      inference('split', [status(esa)], ['67'])).
% 0.56/0.74  thf('85', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.56/0.74      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 0.56/0.74  thf('86', plain,
% 0.56/0.74      (![X1 : $i]:
% 0.56/0.74         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A)))),
% 0.56/0.74      inference('simpl_trail', [status(thm)], ['73', '85'])).
% 0.56/0.74  thf('87', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['62', '86'])).
% 0.56/0.74  thf('88', plain, ((v1_relat_1 @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.74  thf('90', plain, ($false),
% 0.56/0.74      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.56/0.74  
% 0.56/0.74  % SZS output end Refutation
% 0.56/0.74  
% 0.56/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
