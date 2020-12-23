%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OQMexE8cr6

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:45 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 217 expanded)
%              Number of leaves         :   34 (  82 expanded)
%              Depth                    :   18
%              Number of atoms          :  800 (1586 expanded)
%              Number of equality atoms :   93 ( 201 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( v1_relat_1 @ X56 )
      | ~ ( v1_relat_1 @ X57 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X56 @ X57 ) ) ) ),
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
    ! [X61: $i,X62: $i] :
      ( ~ ( v1_relat_1 @ X61 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X61 @ X62 ) )
        = ( k2_relat_1 @ X62 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X62 ) @ ( k2_relat_1 @ X61 ) )
      | ~ ( v1_relat_1 @ X62 ) ) ),
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
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
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
    ! [X53: $i] :
      ( ( v1_relat_1 @ X53 )
      | ( r2_hidden @ ( sk_B @ X53 ) @ X53 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('8',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X35 ) @ X37 )
      | ~ ( r2_hidden @ X35 @ X37 ) ) ),
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
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
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
    ! [X46: $i,X47: $i] :
      ( ( X47 != X46 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X47 ) @ ( k1_tarski @ X46 ) )
       != ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('13',plain,(
    ! [X46: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X46 ) )
     != ( k1_tarski @ X46 ) ) ),
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
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
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
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('18',plain,(
    ! [X46: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X46 ) ) ),
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

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('21',plain,(
    ! [X58: $i] :
      ( ( ( k3_xboole_0 @ X58 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X58 ) @ ( k2_relat_1 @ X58 ) ) )
        = X58 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('23',plain,(
    ! [X58: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X58 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X58 ) @ ( k2_relat_1 @ X58 ) ) ) )
        = X58 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('27',plain,(
    ! [X42: $i,X44: $i,X45: $i] :
      ( ( k2_zfmisc_1 @ X45 @ ( k4_xboole_0 @ X42 @ X44 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X45 @ X42 ) @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('30',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','31'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('33',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('34',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('35',plain,(
    ! [X3: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X3 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['24','32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','36'])).

thf('38',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['11','18'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

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

thf('41',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( v1_relat_1 @ X56 )
      | ~ ( v1_relat_1 @ X57 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X56 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('44',plain,
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

thf('45',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( v1_relat_1 @ X59 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X60 @ X59 ) )
        = ( k1_relat_1 @ X60 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X60 ) @ ( k1_relat_1 @ X59 ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('48',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['11','18'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X58: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X58 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X58 ) @ ( k2_relat_1 @ X58 ) ) ) )
        = X58 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('56',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X42 @ X44 ) @ X43 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X42 @ X43 ) @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('59',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','60'])).

thf('62',plain,(
    ! [X3: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X3 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','63'])).

thf('65',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['11','18'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('69',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('74',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['72','73'])).

thf('75',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['42','74'])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference(simplify,[status(thm)],['78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OQMexE8cr6
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:18:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 222 iterations in 0.087s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.55  thf(dt_k5_relat_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.37/0.55       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (![X56 : $i, X57 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X56)
% 0.37/0.55          | ~ (v1_relat_1 @ X57)
% 0.37/0.55          | (v1_relat_1 @ (k5_relat_1 @ X56 @ X57)))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.37/0.55  thf(t60_relat_1, axiom,
% 0.37/0.55    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.37/0.55     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.55  thf(t47_relat_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( v1_relat_1 @ B ) =>
% 0.37/0.55           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.37/0.55             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X61 : $i, X62 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X61)
% 0.37/0.55          | ((k2_relat_1 @ (k5_relat_1 @ X61 @ X62)) = (k2_relat_1 @ X62))
% 0.37/0.55          | ~ (r1_tarski @ (k1_relat_1 @ X62) @ (k2_relat_1 @ X61))
% 0.37/0.55          | ~ (v1_relat_1 @ X62))),
% 0.37/0.55      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.37/0.55          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.55          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.37/0.55              = (k2_relat_1 @ k1_xboole_0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.55  thf('4', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.37/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.55  thf('5', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.55          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.37/0.55  thf(d1_relat_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ A ) <=>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ~( ( r2_hidden @ B @ A ) & 
% 0.37/0.55              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X53 : $i]: ((v1_relat_1 @ X53) | (r2_hidden @ (sk_B @ X53) @ X53))),
% 0.37/0.55      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.37/0.55  thf(l1_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X35 : $i, X37 : $i]:
% 0.37/0.55         ((r1_tarski @ (k1_tarski @ X35) @ X37) | ~ (r2_hidden @ X35 @ X37))),
% 0.37/0.55      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v1_relat_1 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.55  thf(t3_xboole_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (((v1_relat_1 @ k1_xboole_0)
% 0.37/0.55        | ((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.55  thf(t20_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.55         ( k1_tarski @ A ) ) <=>
% 0.37/0.55       ( ( A ) != ( B ) ) ))).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (![X46 : $i, X47 : $i]:
% 0.37/0.55         (((X47) != (X46))
% 0.37/0.55          | ((k4_xboole_0 @ (k1_tarski @ X47) @ (k1_tarski @ X46))
% 0.37/0.55              != (k1_tarski @ X47)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X46 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ (k1_tarski @ X46) @ (k1_tarski @ X46))
% 0.37/0.55           != (k1_tarski @ X46))),
% 0.37/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.37/0.55  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.55  thf('14', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.55  thf(t100_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X1 @ X2)
% 0.37/0.55           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf(t92_xboole_1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf('17', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.55  thf('18', plain, (![X46 : $i]: ((k1_xboole_0) != (k1_tarski @ X46))),
% 0.37/0.55      inference('demod', [status(thm)], ['13', '16', '17'])).
% 0.37/0.55  thf('19', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.55      inference('clc', [status(thm)], ['11', '18'])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['6', '19'])).
% 0.37/0.55  thf(t22_relat_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ A ) =>
% 0.37/0.55       ( ( k3_xboole_0 @
% 0.37/0.55           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.37/0.55         ( A ) ) ))).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (![X58 : $i]:
% 0.37/0.55         (((k3_xboole_0 @ X58 @ 
% 0.37/0.55            (k2_zfmisc_1 @ (k1_relat_1 @ X58) @ (k2_relat_1 @ X58))) = (
% 0.37/0.55            X58))
% 0.37/0.55          | ~ (v1_relat_1 @ X58))),
% 0.37/0.55      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.37/0.55  thf(t12_setfam_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X49 : $i, X50 : $i]:
% 0.37/0.55         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 0.37/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X58 : $i]:
% 0.37/0.55         (((k1_setfam_1 @ 
% 0.37/0.55            (k2_tarski @ X58 @ 
% 0.37/0.55             (k2_zfmisc_1 @ (k1_relat_1 @ X58) @ (k2_relat_1 @ X58))))
% 0.37/0.55            = (X58))
% 0.37/0.55          | ~ (v1_relat_1 @ X58))),
% 0.37/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k1_setfam_1 @ 
% 0.37/0.55            (k2_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.37/0.55             (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.37/0.55              k1_xboole_0)))
% 0.37/0.55            = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['20', '23'])).
% 0.37/0.55  thf('25', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf(t125_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.37/0.55         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.37/0.55       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.55         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (![X42 : $i, X44 : $i, X45 : $i]:
% 0.37/0.55         ((k2_zfmisc_1 @ X45 @ (k4_xboole_0 @ X42 @ X44))
% 0.37/0.55           = (k4_xboole_0 @ (k2_zfmisc_1 @ X45 @ X42) @ 
% 0.37/0.55              (k2_zfmisc_1 @ X45 @ X44)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.37/0.55           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf('30', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k2_zfmisc_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['25', '31'])).
% 0.37/0.55  thf(t2_boole, axiom,
% 0.37/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X49 : $i, X50 : $i]:
% 0.37/0.55         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 0.37/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      (![X3 : $i]:
% 0.37/0.55         ((k1_setfam_1 @ (k2_tarski @ X3 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['33', '34'])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['24', '32', '35'])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['0', '36'])).
% 0.37/0.55  thf('38', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.55      inference('clc', [status(thm)], ['11', '18'])).
% 0.37/0.55  thf('39', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['39'])).
% 0.37/0.55  thf(t62_relat_1, conjecture,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ A ) =>
% 0.37/0.55       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.37/0.55         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i]:
% 0.37/0.55        ( ( v1_relat_1 @ A ) =>
% 0.37/0.55          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.37/0.55            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.37/0.55        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('42', plain,
% 0.37/0.55      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.55         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.55      inference('split', [status(esa)], ['41'])).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      (![X56 : $i, X57 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X56)
% 0.37/0.55          | ~ (v1_relat_1 @ X57)
% 0.37/0.55          | (v1_relat_1 @ (k5_relat_1 @ X56 @ X57)))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.37/0.55  thf('44', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.55  thf(t46_relat_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( v1_relat_1 @ B ) =>
% 0.37/0.55           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.37/0.55             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.37/0.55  thf('45', plain,
% 0.37/0.55      (![X59 : $i, X60 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X59)
% 0.37/0.55          | ((k1_relat_1 @ (k5_relat_1 @ X60 @ X59)) = (k1_relat_1 @ X60))
% 0.37/0.55          | ~ (r1_tarski @ (k2_relat_1 @ X60) @ (k1_relat_1 @ X59))
% 0.37/0.55          | ~ (v1_relat_1 @ X60))),
% 0.37/0.55      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.37/0.55  thf('46', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.37/0.55          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.55          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.55              = (k1_relat_1 @ k1_xboole_0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.37/0.55  thf('47', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.37/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.55  thf('48', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.55  thf('49', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.55          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.37/0.55  thf('50', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.55      inference('clc', [status(thm)], ['11', '18'])).
% 0.37/0.55  thf('51', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['49', '50'])).
% 0.37/0.55  thf('52', plain,
% 0.37/0.55      (![X58 : $i]:
% 0.37/0.55         (((k1_setfam_1 @ 
% 0.37/0.55            (k2_tarski @ X58 @ 
% 0.37/0.55             (k2_zfmisc_1 @ (k1_relat_1 @ X58) @ (k2_relat_1 @ X58))))
% 0.37/0.55            = (X58))
% 0.37/0.55          | ~ (v1_relat_1 @ X58))),
% 0.37/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('53', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k1_setfam_1 @ 
% 0.37/0.55            (k2_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.37/0.55             (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.37/0.55              (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))))
% 0.37/0.55            = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['51', '52'])).
% 0.37/0.55  thf('54', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.55  thf('55', plain,
% 0.37/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf('56', plain,
% 0.37/0.55      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.37/0.55         ((k2_zfmisc_1 @ (k4_xboole_0 @ X42 @ X44) @ X43)
% 0.37/0.55           = (k4_xboole_0 @ (k2_zfmisc_1 @ X42 @ X43) @ 
% 0.37/0.55              (k2_zfmisc_1 @ X44 @ X43)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.37/0.55  thf('57', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 0.37/0.55           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['55', '56'])).
% 0.37/0.55  thf('58', plain,
% 0.37/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf('59', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.55  thf('60', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.37/0.55  thf('61', plain,
% 0.37/0.55      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['54', '60'])).
% 0.37/0.55  thf('62', plain,
% 0.37/0.55      (![X3 : $i]:
% 0.37/0.55         ((k1_setfam_1 @ (k2_tarski @ X3 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['33', '34'])).
% 0.37/0.55  thf('63', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['53', '61', '62'])).
% 0.37/0.55  thf('64', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['43', '63'])).
% 0.37/0.55  thf('65', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.55      inference('clc', [status(thm)], ['11', '18'])).
% 0.37/0.55  thf('66', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['64', '65'])).
% 0.37/0.55  thf('67', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['66'])).
% 0.37/0.55  thf('68', plain,
% 0.37/0.55      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.37/0.55         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.55      inference('split', [status(esa)], ['41'])).
% 0.37/0.55  thf('69', plain,
% 0.37/0.55      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.37/0.55         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['67', '68'])).
% 0.37/0.55  thf('70', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('71', plain,
% 0.37/0.55      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.55         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.55      inference('demod', [status(thm)], ['69', '70'])).
% 0.37/0.55  thf('72', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['71'])).
% 0.37/0.55  thf('73', plain,
% 0.37/0.55      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.37/0.55       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.55      inference('split', [status(esa)], ['41'])).
% 0.37/0.55  thf('74', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['72', '73'])).
% 0.37/0.55  thf('75', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['42', '74'])).
% 0.37/0.55  thf('76', plain,
% 0.37/0.55      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['40', '75'])).
% 0.37/0.55  thf('77', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('78', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['76', '77'])).
% 0.37/0.55  thf('79', plain, ($false), inference('simplify', [status(thm)], ['78'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
