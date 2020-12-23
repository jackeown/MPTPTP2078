%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hc15k4tAhH

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:41 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 158 expanded)
%              Number of leaves         :   29 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  655 ( 997 expanded)
%              Number of equality atoms :   51 (  88 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_relat_1 @ X31 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X35 @ X34 ) ) @ ( k2_relat_1 @ X34 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('4',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ X27 )
      | ( r2_hidden @ ( sk_B @ X27 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X22 @ X23 ) @ X24 )
      | ~ ( r2_hidden @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('7',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','8'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) )
      | ~ ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X33: $i] :
      ( ( r1_tarski @ X33 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

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

thf('32',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_relat_1 @ X31 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('40',plain,
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

thf('41',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X37 @ X36 ) )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ ( k1_relat_1 @ X36 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('44',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('45',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X32 ) )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','50'])).

thf('52',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('57',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('68',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['38','68'])).

thf('70',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','69'])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('72',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['70','71','72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hc15k4tAhH
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.21/0.35  % CPULimit   : 60
% 0.21/0.35  % DateTime   : Tue Dec  1 17:11:36 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.71/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.71/0.88  % Solved by: fo/fo7.sh
% 0.71/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.88  % done 865 iterations in 0.439s
% 0.71/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.71/0.88  % SZS output start Refutation
% 0.71/0.88  thf(sk_B_type, type, sk_B: $i > $i).
% 0.71/0.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.71/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.71/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.71/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.71/0.88  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.71/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.88  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.71/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.71/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.88  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.71/0.88  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.71/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.88  thf(dt_k5_relat_1, axiom,
% 0.71/0.88    (![A:$i,B:$i]:
% 0.71/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.71/0.88       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.71/0.88  thf('0', plain,
% 0.71/0.88      (![X30 : $i, X31 : $i]:
% 0.71/0.88         (~ (v1_relat_1 @ X30)
% 0.71/0.88          | ~ (v1_relat_1 @ X31)
% 0.71/0.88          | (v1_relat_1 @ (k5_relat_1 @ X30 @ X31)))),
% 0.71/0.88      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.71/0.88  thf(t60_relat_1, axiom,
% 0.71/0.88    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.71/0.88     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.71/0.88  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.88      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.71/0.88  thf(t45_relat_1, axiom,
% 0.71/0.88    (![A:$i]:
% 0.71/0.88     ( ( v1_relat_1 @ A ) =>
% 0.71/0.88       ( ![B:$i]:
% 0.71/0.88         ( ( v1_relat_1 @ B ) =>
% 0.71/0.88           ( r1_tarski @
% 0.71/0.88             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.71/0.88  thf('2', plain,
% 0.71/0.88      (![X34 : $i, X35 : $i]:
% 0.71/0.88         (~ (v1_relat_1 @ X34)
% 0.71/0.88          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X35 @ X34)) @ 
% 0.71/0.88             (k2_relat_1 @ X34))
% 0.71/0.88          | ~ (v1_relat_1 @ X35))),
% 0.71/0.88      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.71/0.88  thf('3', plain,
% 0.71/0.88      (![X0 : $i]:
% 0.71/0.88         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.71/0.88           k1_xboole_0)
% 0.71/0.88          | ~ (v1_relat_1 @ X0)
% 0.71/0.88          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.71/0.88      inference('sup+', [status(thm)], ['1', '2'])).
% 0.71/0.88  thf(d1_relat_1, axiom,
% 0.71/0.88    (![A:$i]:
% 0.71/0.88     ( ( v1_relat_1 @ A ) <=>
% 0.71/0.88       ( ![B:$i]:
% 0.71/0.88         ( ~( ( r2_hidden @ B @ A ) & 
% 0.71/0.88              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.71/0.88  thf('4', plain,
% 0.71/0.88      (![X27 : $i]: ((v1_relat_1 @ X27) | (r2_hidden @ (sk_B @ X27) @ X27))),
% 0.71/0.88      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.71/0.88  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.71/0.88  thf('5', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.71/0.88      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.71/0.88  thf(t55_zfmisc_1, axiom,
% 0.71/0.88    (![A:$i,B:$i,C:$i]:
% 0.71/0.88     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.71/0.88  thf('6', plain,
% 0.71/0.88      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.71/0.88         (~ (r1_xboole_0 @ (k2_tarski @ X22 @ X23) @ X24)
% 0.71/0.89          | ~ (r2_hidden @ X22 @ X24))),
% 0.71/0.89      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.71/0.89  thf('7', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.71/0.89      inference('sup-', [status(thm)], ['5', '6'])).
% 0.71/0.89  thf('8', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.71/0.89      inference('sup-', [status(thm)], ['4', '7'])).
% 0.71/0.89  thf('9', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.71/0.89           k1_xboole_0)
% 0.71/0.89          | ~ (v1_relat_1 @ X0))),
% 0.71/0.89      inference('demod', [status(thm)], ['3', '8'])).
% 0.71/0.89  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.71/0.89  thf('10', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.71/0.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.71/0.89  thf(d10_xboole_0, axiom,
% 0.71/0.89    (![A:$i,B:$i]:
% 0.71/0.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.71/0.89  thf('11', plain,
% 0.71/0.89      (![X1 : $i, X3 : $i]:
% 0.71/0.89         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.71/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.71/0.89  thf('12', plain,
% 0.71/0.89      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['10', '11'])).
% 0.71/0.89  thf('13', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v1_relat_1 @ X0)
% 0.71/0.89          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['9', '12'])).
% 0.71/0.89  thf(fc3_zfmisc_1, axiom,
% 0.71/0.89    (![A:$i,B:$i]:
% 0.71/0.89     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.71/0.89  thf('14', plain,
% 0.71/0.89      (![X20 : $i, X21 : $i]:
% 0.71/0.89         ((v1_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21)) | ~ (v1_xboole_0 @ X21))),
% 0.71/0.89      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.71/0.89  thf(l13_xboole_0, axiom,
% 0.71/0.89    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.71/0.89  thf('15', plain,
% 0.71/0.89      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.71/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.71/0.89  thf('16', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['14', '15'])).
% 0.71/0.89  thf(t21_relat_1, axiom,
% 0.71/0.89    (![A:$i]:
% 0.71/0.89     ( ( v1_relat_1 @ A ) =>
% 0.71/0.89       ( r1_tarski @
% 0.71/0.89         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.71/0.89  thf('17', plain,
% 0.71/0.89      (![X33 : $i]:
% 0.71/0.89         ((r1_tarski @ X33 @ 
% 0.71/0.89           (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33)))
% 0.71/0.89          | ~ (v1_relat_1 @ X33))),
% 0.71/0.89      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.71/0.89  thf('18', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         ((r1_tarski @ X0 @ k1_xboole_0)
% 0.71/0.89          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.71/0.89          | ~ (v1_relat_1 @ X0))),
% 0.71/0.89      inference('sup+', [status(thm)], ['16', '17'])).
% 0.71/0.89  thf('19', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.71/0.89          | ~ (v1_relat_1 @ X0)
% 0.71/0.89          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.71/0.89          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.71/0.89      inference('sup-', [status(thm)], ['13', '18'])).
% 0.71/0.89  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.71/0.89  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.89  thf('21', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v1_relat_1 @ X0)
% 0.71/0.89          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.71/0.89          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.71/0.89      inference('demod', [status(thm)], ['19', '20'])).
% 0.71/0.89  thf('22', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v1_relat_1 @ k1_xboole_0)
% 0.71/0.89          | ~ (v1_relat_1 @ X0)
% 0.71/0.89          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.71/0.89          | ~ (v1_relat_1 @ X0))),
% 0.71/0.89      inference('sup-', [status(thm)], ['0', '21'])).
% 0.71/0.89  thf('23', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.71/0.89      inference('sup-', [status(thm)], ['4', '7'])).
% 0.71/0.89  thf('24', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v1_relat_1 @ X0)
% 0.71/0.89          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.71/0.89          | ~ (v1_relat_1 @ X0))),
% 0.71/0.89      inference('demod', [status(thm)], ['22', '23'])).
% 0.71/0.89  thf('25', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         ((r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.71/0.89          | ~ (v1_relat_1 @ X0))),
% 0.71/0.89      inference('simplify', [status(thm)], ['24'])).
% 0.71/0.89  thf('26', plain,
% 0.71/0.89      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['10', '11'])).
% 0.71/0.89  thf('27', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v1_relat_1 @ X0)
% 0.71/0.89          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['25', '26'])).
% 0.71/0.89  thf('28', plain,
% 0.71/0.89      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.71/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.71/0.89  thf('29', plain,
% 0.71/0.89      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.71/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.71/0.89  thf('30', plain,
% 0.71/0.89      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.71/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.71/0.89  thf('31', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.71/0.89      inference('sup+', [status(thm)], ['29', '30'])).
% 0.71/0.89  thf(t62_relat_1, conjecture,
% 0.71/0.89    (![A:$i]:
% 0.71/0.89     ( ( v1_relat_1 @ A ) =>
% 0.71/0.89       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.71/0.89         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.71/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.89    (~( ![A:$i]:
% 0.71/0.89        ( ( v1_relat_1 @ A ) =>
% 0.71/0.89          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.71/0.89            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.71/0.89    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.71/0.89  thf('32', plain,
% 0.71/0.89      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.71/0.89        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('33', plain,
% 0.71/0.89      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.71/0.89         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.71/0.89      inference('split', [status(esa)], ['32'])).
% 0.71/0.89  thf('34', plain,
% 0.71/0.89      ((![X0 : $i]:
% 0.71/0.89          (((X0) != (k1_xboole_0))
% 0.71/0.89           | ~ (v1_xboole_0 @ X0)
% 0.71/0.89           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 0.71/0.89         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['31', '33'])).
% 0.71/0.89  thf('35', plain,
% 0.71/0.89      (((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.71/0.89         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.71/0.89         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.71/0.89      inference('simplify', [status(thm)], ['34'])).
% 0.71/0.89  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.89  thf('37', plain,
% 0.71/0.89      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 0.71/0.89         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.71/0.89      inference('simplify_reflect+', [status(thm)], ['35', '36'])).
% 0.71/0.89  thf('38', plain,
% 0.71/0.89      ((![X0 : $i]:
% 0.71/0.89          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.71/0.89         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['28', '37'])).
% 0.71/0.89  thf('39', plain,
% 0.71/0.89      (![X30 : $i, X31 : $i]:
% 0.71/0.89         (~ (v1_relat_1 @ X30)
% 0.71/0.89          | ~ (v1_relat_1 @ X31)
% 0.71/0.89          | (v1_relat_1 @ (k5_relat_1 @ X30 @ X31)))),
% 0.71/0.89      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.71/0.89  thf('40', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.89      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.71/0.89  thf(t46_relat_1, axiom,
% 0.71/0.89    (![A:$i]:
% 0.71/0.89     ( ( v1_relat_1 @ A ) =>
% 0.71/0.89       ( ![B:$i]:
% 0.71/0.89         ( ( v1_relat_1 @ B ) =>
% 0.71/0.89           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.71/0.89             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.71/0.89  thf('41', plain,
% 0.71/0.89      (![X36 : $i, X37 : $i]:
% 0.71/0.89         (~ (v1_relat_1 @ X36)
% 0.71/0.89          | ((k1_relat_1 @ (k5_relat_1 @ X37 @ X36)) = (k1_relat_1 @ X37))
% 0.71/0.89          | ~ (r1_tarski @ (k2_relat_1 @ X37) @ (k1_relat_1 @ X36))
% 0.71/0.89          | ~ (v1_relat_1 @ X37))),
% 0.71/0.89      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.71/0.89  thf('42', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.71/0.89          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.71/0.89          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.71/0.89              = (k1_relat_1 @ k1_xboole_0))
% 0.71/0.89          | ~ (v1_relat_1 @ X0))),
% 0.71/0.89      inference('sup-', [status(thm)], ['40', '41'])).
% 0.71/0.89  thf('43', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.71/0.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.71/0.89  thf('44', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.71/0.89      inference('sup-', [status(thm)], ['4', '7'])).
% 0.71/0.89  thf('45', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.89      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.71/0.89  thf('46', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.71/0.89          | ~ (v1_relat_1 @ X0))),
% 0.71/0.89      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.71/0.89  thf(fc8_relat_1, axiom,
% 0.71/0.89    (![A:$i]:
% 0.71/0.89     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.71/0.89       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.71/0.89  thf('47', plain,
% 0.71/0.89      (![X32 : $i]:
% 0.71/0.89         (~ (v1_xboole_0 @ (k1_relat_1 @ X32))
% 0.71/0.89          | ~ (v1_relat_1 @ X32)
% 0.71/0.89          | (v1_xboole_0 @ X32))),
% 0.71/0.89      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.71/0.89  thf('48', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.71/0.89          | ~ (v1_relat_1 @ X0)
% 0.71/0.89          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.71/0.89          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['46', '47'])).
% 0.71/0.89  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.89  thf('50', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v1_relat_1 @ X0)
% 0.71/0.89          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.71/0.89          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.71/0.89      inference('demod', [status(thm)], ['48', '49'])).
% 0.71/0.89  thf('51', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v1_relat_1 @ X0)
% 0.71/0.89          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.71/0.89          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.71/0.89          | ~ (v1_relat_1 @ X0))),
% 0.71/0.89      inference('sup-', [status(thm)], ['39', '50'])).
% 0.71/0.89  thf('52', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.71/0.89      inference('sup-', [status(thm)], ['4', '7'])).
% 0.71/0.89  thf('53', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v1_relat_1 @ X0)
% 0.71/0.89          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.71/0.89          | ~ (v1_relat_1 @ X0))),
% 0.71/0.89      inference('demod', [status(thm)], ['51', '52'])).
% 0.71/0.89  thf('54', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.71/0.89      inference('simplify', [status(thm)], ['53'])).
% 0.71/0.89  thf('55', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.71/0.89      inference('sup+', [status(thm)], ['29', '30'])).
% 0.71/0.89  thf('56', plain,
% 0.71/0.89      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.71/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.71/0.89  thf('57', plain,
% 0.71/0.89      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.71/0.89         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.71/0.89      inference('split', [status(esa)], ['32'])).
% 0.71/0.89  thf('58', plain,
% 0.71/0.89      ((![X0 : $i]:
% 0.71/0.89          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.71/0.89         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['56', '57'])).
% 0.71/0.89  thf('59', plain,
% 0.71/0.89      ((![X0 : $i, X1 : $i]:
% 0.71/0.89          (((X0) != (k1_xboole_0))
% 0.71/0.89           | ~ (v1_xboole_0 @ X0)
% 0.71/0.89           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.71/0.89           | ~ (v1_xboole_0 @ X1)))
% 0.71/0.89         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['55', '58'])).
% 0.71/0.89  thf('60', plain,
% 0.71/0.89      ((![X1 : $i]:
% 0.71/0.89          (~ (v1_xboole_0 @ X1)
% 0.71/0.89           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.71/0.89           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.71/0.89         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.71/0.89      inference('simplify', [status(thm)], ['59'])).
% 0.71/0.89  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.89  thf('62', plain,
% 0.71/0.89      ((![X1 : $i]:
% 0.71/0.89          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.71/0.89         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.71/0.89      inference('simplify_reflect+', [status(thm)], ['60', '61'])).
% 0.71/0.89  thf('63', plain,
% 0.71/0.89      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.71/0.89         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['54', '62'])).
% 0.71/0.89  thf('64', plain, ((v1_relat_1 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.89  thf('66', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.71/0.89      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.71/0.89  thf('67', plain,
% 0.71/0.89      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.71/0.89       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.71/0.89      inference('split', [status(esa)], ['32'])).
% 0.71/0.89  thf('68', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.71/0.89      inference('sat_resolution*', [status(thm)], ['66', '67'])).
% 0.71/0.89  thf('69', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.71/0.89      inference('simpl_trail', [status(thm)], ['38', '68'])).
% 0.71/0.89  thf('70', plain,
% 0.71/0.89      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.71/0.89        | ~ (v1_relat_1 @ sk_A)
% 0.71/0.89        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.71/0.89      inference('sup-', [status(thm)], ['27', '69'])).
% 0.71/0.89  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.89  thf('72', plain, ((v1_relat_1 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.89  thf('74', plain, ($false),
% 0.71/0.89      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.71/0.89  
% 0.71/0.89  % SZS output end Refutation
% 0.71/0.89  
% 0.71/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
