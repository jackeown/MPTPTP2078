%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iPC2cfbOng

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:41 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 147 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  620 ( 936 expanded)
%              Number of equality atoms :   63 (  95 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ~ ( v1_relat_1 @ X49 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X48 @ X49 ) ) ) ),
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
    ! [X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ X53 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X54 @ X53 ) ) @ ( k2_relat_1 @ X53 ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
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
    ! [X45: $i] :
      ( ( v1_relat_1 @ X45 )
      | ( r2_hidden @ ( sk_B @ X45 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('6',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X38 @ X39 ) @ X40 )
      | ~ ( r2_hidden @ X38 @ X40 ) ) ),
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
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X35 ) )
      | ~ ( v1_xboole_0 @ X35 ) ) ),
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

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('17',plain,(
    ! [X50: $i] :
      ( ( ( k3_xboole_0 @ X50 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) )
        = X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf('29',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ~ ( v1_relat_1 @ X49 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('33',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('34',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X52 @ X51 ) ) @ ( k1_relat_1 @ X52 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X50: $i] :
      ( ( ( k3_xboole_0 @ X50 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) )
        = X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','49'])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('55',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('63',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['31','63'])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('68',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    $false ),
    inference(simplify,[status(thm)],['68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iPC2cfbOng
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:39:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.53  % Solved by: fo/fo7.sh
% 0.37/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.53  % done 206 iterations in 0.089s
% 0.37/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.53  % SZS output start Refutation
% 0.37/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.37/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.53  thf(dt_k5_relat_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.37/0.53       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.37/0.53  thf('0', plain,
% 0.37/0.53      (![X48 : $i, X49 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X48)
% 0.37/0.53          | ~ (v1_relat_1 @ X49)
% 0.37/0.53          | (v1_relat_1 @ (k5_relat_1 @ X48 @ X49)))),
% 0.37/0.53      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.37/0.53  thf(t60_relat_1, axiom,
% 0.37/0.53    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.37/0.53     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.53  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.53  thf(t45_relat_1, axiom,
% 0.37/0.53    (![A:$i]:
% 0.37/0.53     ( ( v1_relat_1 @ A ) =>
% 0.37/0.53       ( ![B:$i]:
% 0.37/0.53         ( ( v1_relat_1 @ B ) =>
% 0.37/0.53           ( r1_tarski @
% 0.37/0.53             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.37/0.53  thf('2', plain,
% 0.37/0.53      (![X53 : $i, X54 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X53)
% 0.37/0.53          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X54 @ X53)) @ 
% 0.37/0.53             (k2_relat_1 @ X53))
% 0.37/0.53          | ~ (v1_relat_1 @ X54))),
% 0.37/0.53      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.37/0.53  thf('3', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.37/0.53           k1_xboole_0)
% 0.37/0.53          | ~ (v1_relat_1 @ X0)
% 0.37/0.53          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.53      inference('sup+', [status(thm)], ['1', '2'])).
% 0.37/0.53  thf(d1_relat_1, axiom,
% 0.37/0.53    (![A:$i]:
% 0.37/0.53     ( ( v1_relat_1 @ A ) <=>
% 0.37/0.53       ( ![B:$i]:
% 0.37/0.53         ( ~( ( r2_hidden @ B @ A ) & 
% 0.37/0.53              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.37/0.53  thf('4', plain,
% 0.37/0.53      (![X45 : $i]: ((v1_relat_1 @ X45) | (r2_hidden @ (sk_B @ X45) @ X45))),
% 0.37/0.53      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.37/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.37/0.53  thf('5', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.37/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.53  thf(t55_zfmisc_1, axiom,
% 0.37/0.53    (![A:$i,B:$i,C:$i]:
% 0.37/0.53     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.37/0.53  thf('6', plain,
% 0.37/0.53      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.37/0.53         (~ (r1_xboole_0 @ (k2_tarski @ X38 @ X39) @ X40)
% 0.37/0.53          | ~ (r2_hidden @ X38 @ X40))),
% 0.37/0.53      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.37/0.53  thf('7', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.37/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.53  thf('8', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.53      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.53  thf('9', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.37/0.53           k1_xboole_0)
% 0.37/0.53          | ~ (v1_relat_1 @ X0))),
% 0.37/0.53      inference('demod', [status(thm)], ['3', '8'])).
% 0.37/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.53  thf('10', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.37/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.53  thf(d10_xboole_0, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.53  thf('11', plain,
% 0.37/0.53      (![X1 : $i, X3 : $i]:
% 0.37/0.53         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.37/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.53  thf('12', plain,
% 0.37/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.53  thf('13', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X0)
% 0.37/0.53          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['9', '12'])).
% 0.37/0.53  thf(fc3_zfmisc_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.37/0.53  thf('14', plain,
% 0.37/0.53      (![X34 : $i, X35 : $i]:
% 0.37/0.53         ((v1_xboole_0 @ (k2_zfmisc_1 @ X34 @ X35)) | ~ (v1_xboole_0 @ X35))),
% 0.37/0.53      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.37/0.53  thf(l13_xboole_0, axiom,
% 0.37/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.53  thf('15', plain,
% 0.37/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.53      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.53  thf('16', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.53  thf(t22_relat_1, axiom,
% 0.37/0.53    (![A:$i]:
% 0.37/0.53     ( ( v1_relat_1 @ A ) =>
% 0.37/0.53       ( ( k3_xboole_0 @
% 0.37/0.53           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.37/0.53         ( A ) ) ))).
% 0.37/0.53  thf('17', plain,
% 0.37/0.53      (![X50 : $i]:
% 0.37/0.53         (((k3_xboole_0 @ X50 @ 
% 0.37/0.53            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))) = (
% 0.37/0.53            X50))
% 0.37/0.53          | ~ (v1_relat_1 @ X50))),
% 0.37/0.53      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.37/0.53  thf('18', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.37/0.53          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.37/0.53          | ~ (v1_relat_1 @ X0))),
% 0.37/0.53      inference('sup+', [status(thm)], ['16', '17'])).
% 0.37/0.53  thf(t2_boole, axiom,
% 0.37/0.53    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.53  thf('19', plain,
% 0.37/0.53      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.37/0.53  thf('20', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((k1_xboole_0) = (X0))
% 0.37/0.53          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.37/0.53          | ~ (v1_relat_1 @ X0))),
% 0.37/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.53  thf('21', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.53          | ~ (v1_relat_1 @ X0)
% 0.37/0.53          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.37/0.53          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['13', '20'])).
% 0.37/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.53  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.53  thf('23', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X0)
% 0.37/0.53          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.37/0.53          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.37/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.37/0.53  thf('24', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.53          | ~ (v1_relat_1 @ X0)
% 0.37/0.53          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.37/0.53          | ~ (v1_relat_1 @ X0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['0', '23'])).
% 0.37/0.53  thf('25', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.53      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.53  thf('26', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X0)
% 0.37/0.53          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.37/0.53          | ~ (v1_relat_1 @ X0))),
% 0.37/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.53  thf('27', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.37/0.53          | ~ (v1_relat_1 @ X0))),
% 0.37/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.37/0.53  thf('28', plain,
% 0.37/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.53      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.53  thf(t62_relat_1, conjecture,
% 0.37/0.53    (![A:$i]:
% 0.37/0.53     ( ( v1_relat_1 @ A ) =>
% 0.37/0.53       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.37/0.53         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.53    (~( ![A:$i]:
% 0.37/0.53        ( ( v1_relat_1 @ A ) =>
% 0.37/0.53          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.37/0.53            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.37/0.53    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.37/0.53  thf('29', plain,
% 0.37/0.53      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.37/0.53        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('30', plain,
% 0.37/0.53      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.53         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.53      inference('split', [status(esa)], ['29'])).
% 0.37/0.53  thf('31', plain,
% 0.37/0.53      ((![X0 : $i]:
% 0.37/0.53          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.37/0.53         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['28', '30'])).
% 0.37/0.53  thf('32', plain,
% 0.37/0.53      (![X48 : $i, X49 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X48)
% 0.37/0.53          | ~ (v1_relat_1 @ X49)
% 0.37/0.53          | (v1_relat_1 @ (k5_relat_1 @ X48 @ X49)))),
% 0.37/0.53      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.37/0.53  thf('33', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.53  thf(t44_relat_1, axiom,
% 0.37/0.53    (![A:$i]:
% 0.37/0.53     ( ( v1_relat_1 @ A ) =>
% 0.37/0.53       ( ![B:$i]:
% 0.37/0.53         ( ( v1_relat_1 @ B ) =>
% 0.37/0.53           ( r1_tarski @
% 0.37/0.53             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.37/0.53  thf('34', plain,
% 0.37/0.53      (![X51 : $i, X52 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X51)
% 0.37/0.53          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X52 @ X51)) @ 
% 0.37/0.53             (k1_relat_1 @ X52))
% 0.37/0.53          | ~ (v1_relat_1 @ X52))),
% 0.37/0.53      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.37/0.53  thf('35', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.37/0.53           k1_xboole_0)
% 0.37/0.53          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.53          | ~ (v1_relat_1 @ X0))),
% 0.37/0.53      inference('sup+', [status(thm)], ['33', '34'])).
% 0.37/0.53  thf('36', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.53      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.53  thf('37', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.37/0.53           k1_xboole_0)
% 0.37/0.53          | ~ (v1_relat_1 @ X0))),
% 0.37/0.53      inference('demod', [status(thm)], ['35', '36'])).
% 0.37/0.53  thf('38', plain,
% 0.37/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.53  thf('39', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X0)
% 0.37/0.53          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.53  thf(fc4_zfmisc_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.37/0.53  thf('40', plain,
% 0.37/0.53      (![X36 : $i, X37 : $i]:
% 0.37/0.53         (~ (v1_xboole_0 @ X36) | (v1_xboole_0 @ (k2_zfmisc_1 @ X36 @ X37)))),
% 0.37/0.53      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.37/0.53  thf('41', plain,
% 0.37/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.53      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.53  thf('42', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.53  thf('43', plain,
% 0.37/0.53      (![X50 : $i]:
% 0.37/0.53         (((k3_xboole_0 @ X50 @ 
% 0.37/0.53            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))) = (
% 0.37/0.53            X50))
% 0.37/0.53          | ~ (v1_relat_1 @ X50))),
% 0.37/0.53      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.37/0.53  thf('44', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.37/0.53          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.37/0.53          | ~ (v1_relat_1 @ X0))),
% 0.37/0.53      inference('sup+', [status(thm)], ['42', '43'])).
% 0.37/0.53  thf('45', plain,
% 0.37/0.53      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.37/0.53  thf('46', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((k1_xboole_0) = (X0))
% 0.37/0.53          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.37/0.53          | ~ (v1_relat_1 @ X0))),
% 0.37/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.37/0.53  thf('47', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.53          | ~ (v1_relat_1 @ X0)
% 0.37/0.53          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.53          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['39', '46'])).
% 0.37/0.53  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.53  thf('49', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X0)
% 0.37/0.53          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.53          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.37/0.53      inference('demod', [status(thm)], ['47', '48'])).
% 0.37/0.53  thf('50', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X0)
% 0.37/0.53          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.53          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.53          | ~ (v1_relat_1 @ X0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['32', '49'])).
% 0.37/0.53  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.53      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.53  thf('52', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X0)
% 0.37/0.53          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.53          | ~ (v1_relat_1 @ X0))),
% 0.37/0.53      inference('demod', [status(thm)], ['50', '51'])).
% 0.37/0.53  thf('53', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.53          | ~ (v1_relat_1 @ X0))),
% 0.37/0.53      inference('simplify', [status(thm)], ['52'])).
% 0.37/0.53  thf('54', plain,
% 0.37/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.53      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.53  thf('55', plain,
% 0.37/0.53      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.37/0.53         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.53      inference('split', [status(esa)], ['29'])).
% 0.37/0.53  thf('56', plain,
% 0.37/0.53      ((![X0 : $i]:
% 0.37/0.53          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.37/0.53         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['54', '55'])).
% 0.37/0.53  thf('57', plain,
% 0.37/0.53      (((((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.53         | ~ (v1_relat_1 @ sk_A)
% 0.37/0.53         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.37/0.53         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['53', '56'])).
% 0.37/0.53  thf('58', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.53  thf('60', plain,
% 0.37/0.53      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.53         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.53      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.37/0.53  thf('61', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.53      inference('simplify', [status(thm)], ['60'])).
% 0.37/0.53  thf('62', plain,
% 0.37/0.53      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.37/0.53       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.53      inference('split', [status(esa)], ['29'])).
% 0.37/0.53  thf('63', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.53      inference('sat_resolution*', [status(thm)], ['61', '62'])).
% 0.37/0.53  thf('64', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.53      inference('simpl_trail', [status(thm)], ['31', '63'])).
% 0.37/0.53  thf('65', plain,
% 0.37/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.53        | ~ (v1_relat_1 @ sk_A)
% 0.37/0.53        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['27', '64'])).
% 0.37/0.53  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.53  thf('68', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.53      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.37/0.53  thf('69', plain, ($false), inference('simplify', [status(thm)], ['68'])).
% 0.37/0.53  
% 0.37/0.53  % SZS output end Refutation
% 0.37/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
