%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IZ2n9fe1eG

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 143 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  604 ( 915 expanded)
%              Number of equality atoms :   48 (  82 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X28 @ X29 ) ) ) ),
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

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X35 @ X34 ) )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ ( k1_relat_1 @ X34 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('5',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ X25 )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X20 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('8',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','9','10'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X30: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
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

thf('24',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('32',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('33',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X33 @ X32 ) ) @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X31: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','44'])).

thf('46',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('51',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('60',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('62',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['30','62'])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['64','65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IZ2n9fe1eG
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:11:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 279 iterations in 0.135s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.58  thf(dt_k5_relat_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.20/0.58       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      (![X28 : $i, X29 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X28)
% 0.20/0.58          | ~ (v1_relat_1 @ X29)
% 0.20/0.58          | (v1_relat_1 @ (k5_relat_1 @ X28 @ X29)))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.20/0.58  thf(t60_relat_1, axiom,
% 0.20/0.58    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.58     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.58  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.58  thf(t46_relat_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( v1_relat_1 @ B ) =>
% 0.20/0.58           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.58             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      (![X34 : $i, X35 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X34)
% 0.20/0.58          | ((k1_relat_1 @ (k5_relat_1 @ X35 @ X34)) = (k1_relat_1 @ X35))
% 0.20/0.58          | ~ (r1_tarski @ (k2_relat_1 @ X35) @ (k1_relat_1 @ X34))
% 0.20/0.58          | ~ (v1_relat_1 @ X35))),
% 0.20/0.58      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.20/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.58          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.58              = (k1_relat_1 @ k1_xboole_0))
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.58  thf('4', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.58  thf(d1_relat_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ A ) <=>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.58              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      (![X25 : $i]: ((v1_relat_1 @ X25) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 0.20/0.58      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.20/0.58  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.58  thf('6', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.20/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.58  thf(t55_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.58         (~ (r1_xboole_0 @ (k2_tarski @ X20 @ X21) @ X22)
% 0.20/0.58          | ~ (r2_hidden @ X20 @ X22))),
% 0.20/0.58      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.20/0.58  thf('8', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.58  thf('9', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.58  thf('10', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('demod', [status(thm)], ['3', '4', '9', '10'])).
% 0.20/0.58  thf(fc8_relat_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.20/0.58       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.20/0.58  thf('12', plain,
% 0.20/0.58      (![X30 : $i]:
% 0.20/0.58         (~ (v1_xboole_0 @ (k1_relat_1 @ X30))
% 0.20/0.58          | ~ (v1_relat_1 @ X30)
% 0.20/0.58          | (v1_xboole_0 @ X30))),
% 0.20/0.58      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.58          | ~ (v1_relat_1 @ X0)
% 0.20/0.58          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.58  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.58  thf('15', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.58          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['0', '15'])).
% 0.20/0.58  thf('17', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.58  thf('18', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.58  thf('19', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.58  thf(l13_xboole_0, axiom,
% 0.20/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.58  thf('20', plain,
% 0.20/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.58  thf('21', plain,
% 0.20/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.58      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.58  thf('23', plain,
% 0.20/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.58  thf(t62_relat_1, conjecture,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ A ) =>
% 0.20/0.58       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.20/0.58         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i]:
% 0.20/0.58        ( ( v1_relat_1 @ A ) =>
% 0.20/0.58          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.20/0.58            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.20/0.58  thf('24', plain,
% 0.20/0.58      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.20/0.58        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('25', plain,
% 0.20/0.58      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.20/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.58      inference('split', [status(esa)], ['24'])).
% 0.20/0.58  thf('26', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.20/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.58  thf('27', plain,
% 0.20/0.58      ((![X0 : $i, X1 : $i]:
% 0.20/0.58          (((X0) != (k1_xboole_0))
% 0.20/0.58           | ~ (v1_xboole_0 @ X0)
% 0.20/0.58           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.20/0.58           | ~ (v1_xboole_0 @ X1)))
% 0.20/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['22', '26'])).
% 0.20/0.58  thf('28', plain,
% 0.20/0.58      ((![X1 : $i]:
% 0.20/0.58          (~ (v1_xboole_0 @ X1)
% 0.20/0.58           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.20/0.58           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.20/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.58  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.58  thf('30', plain,
% 0.20/0.58      ((![X1 : $i]:
% 0.20/0.58          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.20/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.58      inference('simplify_reflect+', [status(thm)], ['28', '29'])).
% 0.20/0.58  thf('31', plain,
% 0.20/0.58      (![X28 : $i, X29 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X28)
% 0.20/0.58          | ~ (v1_relat_1 @ X29)
% 0.20/0.58          | (v1_relat_1 @ (k5_relat_1 @ X28 @ X29)))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.20/0.58  thf('32', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.58  thf(t45_relat_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( v1_relat_1 @ B ) =>
% 0.20/0.58           ( r1_tarski @
% 0.20/0.58             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.20/0.58  thf('33', plain,
% 0.20/0.58      (![X32 : $i, X33 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X32)
% 0.20/0.58          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X33 @ X32)) @ 
% 0.20/0.58             (k2_relat_1 @ X32))
% 0.20/0.58          | ~ (v1_relat_1 @ X33))),
% 0.20/0.58      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.20/0.58           k1_xboole_0)
% 0.20/0.58          | ~ (v1_relat_1 @ X0)
% 0.20/0.58          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.58  thf('35', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.58  thf('36', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.20/0.58           k1_xboole_0)
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.58  thf('37', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.58  thf(d10_xboole_0, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.58  thf('38', plain,
% 0.20/0.58      (![X1 : $i, X3 : $i]:
% 0.20/0.58         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.20/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.58  thf('39', plain,
% 0.20/0.58      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.58  thf('40', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['36', '39'])).
% 0.20/0.58  thf(fc9_relat_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.20/0.58       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.20/0.58  thf('41', plain,
% 0.20/0.58      (![X31 : $i]:
% 0.20/0.58         (~ (v1_xboole_0 @ (k2_relat_1 @ X31))
% 0.20/0.58          | ~ (v1_relat_1 @ X31)
% 0.20/0.58          | (v1_xboole_0 @ X31))),
% 0.20/0.58      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.20/0.58  thf('42', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.58          | ~ (v1_relat_1 @ X0)
% 0.20/0.58          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.58  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.58  thf('44', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.58  thf('45', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.58          | ~ (v1_relat_1 @ X0)
% 0.20/0.58          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['31', '44'])).
% 0.20/0.58  thf('46', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.58  thf('47', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.58  thf('48', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.58  thf('49', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.58      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.58  thf('50', plain,
% 0.20/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.58  thf('51', plain,
% 0.20/0.58      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.58      inference('split', [status(esa)], ['24'])).
% 0.20/0.58  thf('52', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.20/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.58  thf('53', plain,
% 0.20/0.58      ((![X0 : $i, X1 : $i]:
% 0.20/0.58          (((X0) != (k1_xboole_0))
% 0.20/0.58           | ~ (v1_xboole_0 @ X0)
% 0.20/0.58           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.20/0.58           | ~ (v1_xboole_0 @ X1)))
% 0.20/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['49', '52'])).
% 0.20/0.58  thf('54', plain,
% 0.20/0.58      ((![X1 : $i]:
% 0.20/0.58          (~ (v1_xboole_0 @ X1)
% 0.20/0.58           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.20/0.58           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.20/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.58  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.58  thf('56', plain,
% 0.20/0.58      ((![X1 : $i]:
% 0.20/0.58          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))))
% 0.20/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.58      inference('simplify_reflect+', [status(thm)], ['54', '55'])).
% 0.20/0.58  thf('57', plain,
% 0.20/0.58      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.20/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['48', '56'])).
% 0.20/0.58  thf('58', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.58  thf('60', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.20/0.58  thf('61', plain,
% 0.20/0.58      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.58       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.58      inference('split', [status(esa)], ['24'])).
% 0.20/0.58  thf('62', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['60', '61'])).
% 0.20/0.58  thf('63', plain,
% 0.20/0.58      (![X1 : $i]:
% 0.20/0.58         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A)))),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['30', '62'])).
% 0.20/0.58  thf('64', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['19', '63'])).
% 0.20/0.58  thf('65', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.58  thf('67', plain, ($false),
% 0.20/0.58      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
