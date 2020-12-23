%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.70snYBf8M2

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:43 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 194 expanded)
%              Number of leaves         :   35 (  73 expanded)
%              Depth                    :   18
%              Number of atoms          :  729 (1322 expanded)
%              Number of equality atoms :   85 ( 167 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ X53 )
      | ~ ( v1_relat_1 @ X54 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X53 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X58 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X58 @ X59 ) )
        = ( k2_relat_1 @ X59 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X59 ) @ ( k2_relat_1 @ X58 ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('5',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('7',plain,(
    ! [X50: $i] :
      ( ( v1_relat_1 @ X50 )
      | ( r2_hidden @ ( sk_B @ X50 ) @ X50 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('8',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X40 ) @ X42 )
      | ~ ( r2_hidden @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('11',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_tarski @ ( sk_B @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('12',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X44 != X43 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X44 ) @ ( k1_tarski @ X43 ) )
       != ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('13',plain,(
    ! [X43: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X43 ) )
     != ( k1_tarski @ X43 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('18',plain,(
    ! [X43: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X43 ) ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('19',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','19'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X36 @ X37 ) )
      | ~ ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('24',plain,(
    ! [X55: $i] :
      ( ( ( k3_xboole_0 @ X55 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) )
        = X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','30'])).

thf('32',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['11','18'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
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

thf('36',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ X53 )
      | ~ ( v1_relat_1 @ X54 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X53 @ X54 ) ) ) ),
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
    ! [X56: $i,X57: $i] :
      ( ~ ( v1_relat_1 @ X56 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X57 @ X56 ) )
        = ( k1_relat_1 @ X57 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X57 ) @ ( k1_relat_1 @ X56 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
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
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('44',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['11','18'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('49',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X55: $i] :
      ( ( ( k3_xboole_0 @ X55 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) )
        = X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','57'])).

thf('59',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['11','18'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('63',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('68',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('71',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['38','71'])).

thf('73',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    $false ),
    inference(simplify,[status(thm)],['76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.70snYBf8M2
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:55:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.67/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.88  % Solved by: fo/fo7.sh
% 0.67/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.88  % done 889 iterations in 0.428s
% 0.67/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.88  % SZS output start Refutation
% 0.67/0.88  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.67/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.67/0.88  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.67/0.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.67/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.67/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.67/0.88  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.67/0.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.67/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.88  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.67/0.88  thf(sk_B_type, type, sk_B: $i > $i).
% 0.67/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.88  thf(dt_k5_relat_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.67/0.88       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.67/0.88  thf('0', plain,
% 0.67/0.88      (![X53 : $i, X54 : $i]:
% 0.67/0.88         (~ (v1_relat_1 @ X53)
% 0.67/0.88          | ~ (v1_relat_1 @ X54)
% 0.67/0.88          | (v1_relat_1 @ (k5_relat_1 @ X53 @ X54)))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.67/0.88  thf(t60_relat_1, axiom,
% 0.67/0.88    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.67/0.88     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.67/0.88  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.88      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.67/0.88  thf(t47_relat_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( v1_relat_1 @ A ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( v1_relat_1 @ B ) =>
% 0.67/0.88           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.67/0.88             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.67/0.88  thf('2', plain,
% 0.67/0.88      (![X58 : $i, X59 : $i]:
% 0.67/0.88         (~ (v1_relat_1 @ X58)
% 0.67/0.88          | ((k2_relat_1 @ (k5_relat_1 @ X58 @ X59)) = (k2_relat_1 @ X59))
% 0.67/0.88          | ~ (r1_tarski @ (k1_relat_1 @ X59) @ (k2_relat_1 @ X58))
% 0.67/0.88          | ~ (v1_relat_1 @ X59))),
% 0.67/0.88      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.67/0.88  thf('3', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.67/0.88          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.67/0.88          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.67/0.88              = (k2_relat_1 @ k1_xboole_0))
% 0.67/0.88          | ~ (v1_relat_1 @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.67/0.88  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.67/0.88  thf('4', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.67/0.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.67/0.88  thf('5', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.88      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.67/0.88  thf('6', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (v1_relat_1 @ k1_xboole_0)
% 0.67/0.88          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.67/0.88          | ~ (v1_relat_1 @ X0))),
% 0.67/0.88      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.67/0.88  thf(d1_relat_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( v1_relat_1 @ A ) <=>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ~( ( r2_hidden @ B @ A ) & 
% 0.67/0.88              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.67/0.88  thf('7', plain,
% 0.67/0.88      (![X50 : $i]: ((v1_relat_1 @ X50) | (r2_hidden @ (sk_B @ X50) @ X50))),
% 0.67/0.88      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.67/0.88  thf(l1_zfmisc_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.67/0.88  thf('8', plain,
% 0.67/0.88      (![X40 : $i, X42 : $i]:
% 0.67/0.88         ((r1_tarski @ (k1_tarski @ X40) @ X42) | ~ (r2_hidden @ X40 @ X42))),
% 0.67/0.88      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.67/0.88  thf('9', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((v1_relat_1 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['7', '8'])).
% 0.67/0.88  thf(t3_xboole_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.67/0.88  thf('10', plain,
% 0.67/0.88      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 0.67/0.88      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.67/0.88  thf('11', plain,
% 0.67/0.88      (((v1_relat_1 @ k1_xboole_0)
% 0.67/0.88        | ((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['9', '10'])).
% 0.67/0.88  thf(t20_zfmisc_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.67/0.88         ( k1_tarski @ A ) ) <=>
% 0.67/0.88       ( ( A ) != ( B ) ) ))).
% 0.67/0.88  thf('12', plain,
% 0.67/0.88      (![X43 : $i, X44 : $i]:
% 0.67/0.88         (((X44) != (X43))
% 0.67/0.88          | ((k4_xboole_0 @ (k1_tarski @ X44) @ (k1_tarski @ X43))
% 0.67/0.88              != (k1_tarski @ X44)))),
% 0.67/0.88      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.67/0.88  thf('13', plain,
% 0.67/0.88      (![X43 : $i]:
% 0.67/0.88         ((k4_xboole_0 @ (k1_tarski @ X43) @ (k1_tarski @ X43))
% 0.67/0.88           != (k1_tarski @ X43))),
% 0.67/0.88      inference('simplify', [status(thm)], ['12'])).
% 0.67/0.88  thf(idempotence_k3_xboole_0, axiom,
% 0.67/0.88    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.67/0.88  thf('14', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.67/0.88      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.67/0.88  thf(t100_xboole_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.67/0.88  thf('15', plain,
% 0.67/0.88      (![X2 : $i, X3 : $i]:
% 0.67/0.88         ((k4_xboole_0 @ X2 @ X3)
% 0.67/0.88           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.67/0.88      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.67/0.88  thf('16', plain,
% 0.67/0.88      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.67/0.88      inference('sup+', [status(thm)], ['14', '15'])).
% 0.67/0.88  thf(t92_xboole_1, axiom,
% 0.67/0.88    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.67/0.88  thf('17', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.67/0.88      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.67/0.88  thf('18', plain, (![X43 : $i]: ((k1_xboole_0) != (k1_tarski @ X43))),
% 0.67/0.88      inference('demod', [status(thm)], ['13', '16', '17'])).
% 0.67/0.88  thf('19', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.67/0.88      inference('clc', [status(thm)], ['11', '18'])).
% 0.67/0.88  thf('20', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.67/0.88          | ~ (v1_relat_1 @ X0))),
% 0.67/0.88      inference('demod', [status(thm)], ['6', '19'])).
% 0.67/0.88  thf(fc3_zfmisc_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.67/0.88  thf('21', plain,
% 0.67/0.88      (![X36 : $i, X37 : $i]:
% 0.67/0.88         ((v1_xboole_0 @ (k2_zfmisc_1 @ X36 @ X37)) | ~ (v1_xboole_0 @ X37))),
% 0.67/0.88      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.67/0.88  thf(l13_xboole_0, axiom,
% 0.67/0.88    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.67/0.88  thf('22', plain,
% 0.67/0.88      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.67/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.67/0.88  thf('23', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['21', '22'])).
% 0.67/0.88  thf(t22_relat_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( v1_relat_1 @ A ) =>
% 0.67/0.88       ( ( k3_xboole_0 @
% 0.67/0.88           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.67/0.88         ( A ) ) ))).
% 0.67/0.88  thf('24', plain,
% 0.67/0.88      (![X55 : $i]:
% 0.67/0.88         (((k3_xboole_0 @ X55 @ 
% 0.67/0.88            (k2_zfmisc_1 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))) = (
% 0.67/0.88            X55))
% 0.67/0.88          | ~ (v1_relat_1 @ X55))),
% 0.67/0.88      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.67/0.88  thf('25', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.67/0.88          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.67/0.88          | ~ (v1_relat_1 @ X0))),
% 0.67/0.88      inference('sup+', [status(thm)], ['23', '24'])).
% 0.67/0.88  thf(t2_boole, axiom,
% 0.67/0.88    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.67/0.88  thf('26', plain,
% 0.67/0.88      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.88      inference('cnf', [status(esa)], [t2_boole])).
% 0.67/0.88  thf('27', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (((k1_xboole_0) = (X0))
% 0.67/0.88          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.67/0.88          | ~ (v1_relat_1 @ X0))),
% 0.67/0.88      inference('demod', [status(thm)], ['25', '26'])).
% 0.67/0.88  thf('28', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.67/0.88          | ~ (v1_relat_1 @ X0)
% 0.67/0.88          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.67/0.88          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['20', '27'])).
% 0.67/0.88  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.67/0.88  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.67/0.88  thf('30', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (v1_relat_1 @ X0)
% 0.67/0.88          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.67/0.88          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.67/0.88      inference('demod', [status(thm)], ['28', '29'])).
% 0.67/0.88  thf('31', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (v1_relat_1 @ k1_xboole_0)
% 0.67/0.88          | ~ (v1_relat_1 @ X0)
% 0.67/0.88          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.67/0.88          | ~ (v1_relat_1 @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['0', '30'])).
% 0.67/0.88  thf('32', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.67/0.88      inference('clc', [status(thm)], ['11', '18'])).
% 0.67/0.88  thf('33', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (v1_relat_1 @ X0)
% 0.67/0.88          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.67/0.88          | ~ (v1_relat_1 @ X0))),
% 0.67/0.88      inference('demod', [status(thm)], ['31', '32'])).
% 0.67/0.88  thf('34', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.67/0.88          | ~ (v1_relat_1 @ X0))),
% 0.67/0.88      inference('simplify', [status(thm)], ['33'])).
% 0.67/0.88  thf('35', plain,
% 0.67/0.88      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.67/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.67/0.88  thf(t62_relat_1, conjecture,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( v1_relat_1 @ A ) =>
% 0.67/0.88       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.67/0.88         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.67/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.88    (~( ![A:$i]:
% 0.67/0.88        ( ( v1_relat_1 @ A ) =>
% 0.67/0.88          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.67/0.88            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.67/0.88    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.67/0.88  thf('36', plain,
% 0.67/0.88      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.67/0.88        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('37', plain,
% 0.67/0.88      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.67/0.89         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.67/0.89      inference('split', [status(esa)], ['36'])).
% 0.67/0.89  thf('38', plain,
% 0.67/0.89      ((![X0 : $i]:
% 0.67/0.89          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.67/0.89         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.67/0.89      inference('sup-', [status(thm)], ['35', '37'])).
% 0.67/0.89  thf('39', plain,
% 0.67/0.89      (![X53 : $i, X54 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ X53)
% 0.67/0.89          | ~ (v1_relat_1 @ X54)
% 0.67/0.89          | (v1_relat_1 @ (k5_relat_1 @ X53 @ X54)))),
% 0.67/0.89      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.67/0.89  thf('40', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.89      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.67/0.89  thf(t46_relat_1, axiom,
% 0.67/0.89    (![A:$i]:
% 0.67/0.89     ( ( v1_relat_1 @ A ) =>
% 0.67/0.89       ( ![B:$i]:
% 0.67/0.89         ( ( v1_relat_1 @ B ) =>
% 0.67/0.89           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.67/0.89             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.67/0.89  thf('41', plain,
% 0.67/0.89      (![X56 : $i, X57 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ X56)
% 0.67/0.89          | ((k1_relat_1 @ (k5_relat_1 @ X57 @ X56)) = (k1_relat_1 @ X57))
% 0.67/0.89          | ~ (r1_tarski @ (k2_relat_1 @ X57) @ (k1_relat_1 @ X56))
% 0.67/0.89          | ~ (v1_relat_1 @ X57))),
% 0.67/0.89      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.67/0.89  thf('42', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.67/0.89          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.67/0.89          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.67/0.89              = (k1_relat_1 @ k1_xboole_0))
% 0.67/0.89          | ~ (v1_relat_1 @ X0))),
% 0.67/0.89      inference('sup-', [status(thm)], ['40', '41'])).
% 0.67/0.89  thf('43', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.67/0.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.67/0.89  thf('44', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.89      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.67/0.89  thf('45', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ k1_xboole_0)
% 0.67/0.89          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.67/0.89          | ~ (v1_relat_1 @ X0))),
% 0.67/0.89      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.67/0.89  thf('46', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.67/0.89      inference('clc', [status(thm)], ['11', '18'])).
% 0.67/0.89  thf('47', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.67/0.89          | ~ (v1_relat_1 @ X0))),
% 0.67/0.89      inference('demod', [status(thm)], ['45', '46'])).
% 0.67/0.89  thf(fc4_zfmisc_1, axiom,
% 0.67/0.89    (![A:$i,B:$i]:
% 0.67/0.89     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.67/0.89  thf('48', plain,
% 0.67/0.89      (![X38 : $i, X39 : $i]:
% 0.67/0.89         (~ (v1_xboole_0 @ X38) | (v1_xboole_0 @ (k2_zfmisc_1 @ X38 @ X39)))),
% 0.67/0.89      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.67/0.89  thf('49', plain,
% 0.67/0.89      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.67/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.67/0.89  thf('50', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]:
% 0.67/0.89         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['48', '49'])).
% 0.67/0.89  thf('51', plain,
% 0.67/0.89      (![X55 : $i]:
% 0.67/0.89         (((k3_xboole_0 @ X55 @ 
% 0.67/0.89            (k2_zfmisc_1 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))) = (
% 0.67/0.89            X55))
% 0.67/0.89          | ~ (v1_relat_1 @ X55))),
% 0.67/0.89      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.67/0.89  thf('52', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.67/0.89          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.67/0.89          | ~ (v1_relat_1 @ X0))),
% 0.67/0.89      inference('sup+', [status(thm)], ['50', '51'])).
% 0.67/0.89  thf('53', plain,
% 0.67/0.89      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.89      inference('cnf', [status(esa)], [t2_boole])).
% 0.67/0.89  thf('54', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (((k1_xboole_0) = (X0))
% 0.67/0.89          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.67/0.89          | ~ (v1_relat_1 @ X0))),
% 0.67/0.89      inference('demod', [status(thm)], ['52', '53'])).
% 0.67/0.89  thf('55', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.67/0.89          | ~ (v1_relat_1 @ X0)
% 0.67/0.89          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.67/0.89          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['47', '54'])).
% 0.67/0.89  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.67/0.89  thf('57', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ X0)
% 0.67/0.89          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.67/0.89          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.67/0.89      inference('demod', [status(thm)], ['55', '56'])).
% 0.67/0.89  thf('58', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ X0)
% 0.67/0.89          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.67/0.89          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.67/0.89          | ~ (v1_relat_1 @ X0))),
% 0.67/0.89      inference('sup-', [status(thm)], ['39', '57'])).
% 0.67/0.89  thf('59', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.67/0.89      inference('clc', [status(thm)], ['11', '18'])).
% 0.67/0.89  thf('60', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ X0)
% 0.67/0.89          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.67/0.89          | ~ (v1_relat_1 @ X0))),
% 0.67/0.89      inference('demod', [status(thm)], ['58', '59'])).
% 0.67/0.89  thf('61', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.67/0.89          | ~ (v1_relat_1 @ X0))),
% 0.67/0.89      inference('simplify', [status(thm)], ['60'])).
% 0.67/0.89  thf('62', plain,
% 0.67/0.89      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.67/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.67/0.89  thf('63', plain,
% 0.67/0.89      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.67/0.89         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.89      inference('split', [status(esa)], ['36'])).
% 0.67/0.89  thf('64', plain,
% 0.67/0.89      ((![X0 : $i]:
% 0.67/0.89          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.67/0.89         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.89      inference('sup-', [status(thm)], ['62', '63'])).
% 0.67/0.89  thf('65', plain,
% 0.67/0.89      (((((k1_xboole_0) != (k1_xboole_0))
% 0.67/0.89         | ~ (v1_relat_1 @ sk_A)
% 0.67/0.89         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.67/0.89         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.89      inference('sup-', [status(thm)], ['61', '64'])).
% 0.67/0.89  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.67/0.89  thf('68', plain,
% 0.67/0.89      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.67/0.89         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.89      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.67/0.89  thf('69', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.67/0.89      inference('simplify', [status(thm)], ['68'])).
% 0.67/0.89  thf('70', plain,
% 0.67/0.89      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.67/0.89       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.67/0.89      inference('split', [status(esa)], ['36'])).
% 0.67/0.89  thf('71', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.67/0.89      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.67/0.89  thf('72', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.89      inference('simpl_trail', [status(thm)], ['38', '71'])).
% 0.67/0.89  thf('73', plain,
% 0.67/0.89      ((((k1_xboole_0) != (k1_xboole_0))
% 0.67/0.89        | ~ (v1_relat_1 @ sk_A)
% 0.67/0.89        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.67/0.89      inference('sup-', [status(thm)], ['34', '72'])).
% 0.67/0.89  thf('74', plain, ((v1_relat_1 @ sk_A)),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.67/0.89  thf('76', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.67/0.89      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.67/0.89  thf('77', plain, ($false), inference('simplify', [status(thm)], ['76'])).
% 0.67/0.89  
% 0.67/0.89  % SZS output end Refutation
% 0.67/0.89  
% 0.71/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
