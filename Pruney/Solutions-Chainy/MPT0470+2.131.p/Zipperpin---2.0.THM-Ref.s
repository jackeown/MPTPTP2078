%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m4VBysIXGm

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 253 expanded)
%              Number of leaves         :   35 (  94 expanded)
%              Depth                    :   20
%              Number of atoms          :  793 (1796 expanded)
%              Number of equality atoms :   94 ( 237 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
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
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ X36 ) ) ),
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
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
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
    ! [X45: $i,X46: $i] :
      ( ( X46 != X45 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X45 ) )
       != ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('13',plain,(
    ! [X45: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X45 ) @ ( k1_tarski @ X45 ) )
     != ( k1_tarski @ X45 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('15',plain,(
    ! [X48: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,(
    ! [X45: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X45 ) ) ),
    inference(demod,[status(thm)],['13','20','21'])).

thf('23',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','23'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('25',plain,(
    ! [X58: $i] :
      ( ( ( k3_xboole_0 @ X58 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X58 ) @ ( k2_relat_1 @ X58 ) ) )
        = X58 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('29',plain,(
    ! [X41: $i,X43: $i,X44: $i] :
      ( ( k2_zfmisc_1 @ X44 @ ( k4_xboole_0 @ X41 @ X43 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X44 @ X41 ) @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('32',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','33'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['26','34','35'])).

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
    inference(clc,[status(thm)],['11','22'])).

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
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
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
    inference(clc,[status(thm)],['11','22'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X58: $i] :
      ( ( ( k3_xboole_0 @ X58 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X58 ) @ ( k2_relat_1 @ X58 ) ) )
        = X58 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('56',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X41 @ X43 ) @ X42 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X41 @ X42 ) @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ),
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
    inference('sup+',[status(thm)],['18','19'])).

thf('59',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
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
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

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
    inference(clc,[status(thm)],['11','22'])).

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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m4VBysIXGm
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:23:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 222 iterations in 0.086s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.54  thf(dt_k5_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.54       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (![X56 : $i, X57 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X56)
% 0.21/0.54          | ~ (v1_relat_1 @ X57)
% 0.21/0.54          | (v1_relat_1 @ (k5_relat_1 @ X56 @ X57)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.54  thf(t60_relat_1, axiom,
% 0.21/0.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.54  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.54  thf(t47_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( v1_relat_1 @ B ) =>
% 0.21/0.54           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.54             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X61 : $i, X62 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X61)
% 0.21/0.54          | ((k2_relat_1 @ (k5_relat_1 @ X61 @ X62)) = (k2_relat_1 @ X62))
% 0.21/0.54          | ~ (r1_tarski @ (k1_relat_1 @ X62) @ (k2_relat_1 @ X61))
% 0.21/0.54          | ~ (v1_relat_1 @ X62))),
% 0.21/0.54      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.54          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.54              = (k2_relat_1 @ k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.54  thf('4', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.54  thf('5', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.54          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.54  thf(d1_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) <=>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.54              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X53 : $i]: ((v1_relat_1 @ X53) | (r2_hidden @ (sk_B @ X53) @ X53))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.21/0.54  thf(l1_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X34 : $i, X36 : $i]:
% 0.21/0.54         ((r1_tarski @ (k1_tarski @ X34) @ X36) | ~ (r2_hidden @ X34 @ X36))),
% 0.21/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_relat_1 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf(t3_xboole_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (((v1_relat_1 @ k1_xboole_0)
% 0.21/0.54        | ((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf(t20_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.54         ( k1_tarski @ A ) ) <=>
% 0.21/0.54       ( ( A ) != ( B ) ) ))).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X45 : $i, X46 : $i]:
% 0.21/0.54         (((X46) != (X45))
% 0.21/0.54          | ((k4_xboole_0 @ (k1_tarski @ X46) @ (k1_tarski @ X45))
% 0.21/0.54              != (k1_tarski @ X46)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X45 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ (k1_tarski @ X45) @ (k1_tarski @ X45))
% 0.21/0.54           != (k1_tarski @ X45))),
% 0.21/0.54      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.54  thf(t69_enumset1, axiom,
% 0.21/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.54  thf('14', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.54  thf(t11_setfam_1, axiom,
% 0.21/0.54    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.21/0.54  thf('15', plain, (![X48 : $i]: ((k1_setfam_1 @ (k1_tarski @ X48)) = (X48))),
% 0.21/0.54      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.54  thf(t12_setfam_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X49 : $i, X50 : $i]:
% 0.21/0.54         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 0.21/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.54  thf('18', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf(t100_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf(t92_xboole_1, axiom,
% 0.21/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.54  thf('21', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.54  thf('22', plain, (![X45 : $i]: ((k1_xboole_0) != (k1_tarski @ X45))),
% 0.21/0.54      inference('demod', [status(thm)], ['13', '20', '21'])).
% 0.21/0.54  thf('23', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.54      inference('clc', [status(thm)], ['11', '22'])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['6', '23'])).
% 0.21/0.54  thf(t22_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ( k3_xboole_0 @
% 0.21/0.54           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.21/0.54         ( A ) ) ))).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X58 : $i]:
% 0.21/0.54         (((k3_xboole_0 @ X58 @ 
% 0.21/0.54            (k2_zfmisc_1 @ (k1_relat_1 @ X58) @ (k2_relat_1 @ X58))) = (
% 0.21/0.54            X58))
% 0.21/0.54          | ~ (v1_relat_1 @ X58))),
% 0.21/0.54      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k3_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.21/0.54            (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.21/0.54             k1_xboole_0))
% 0.21/0.54            = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf('27', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf(t125_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.21/0.54         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.21/0.54       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.54         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X41 : $i, X43 : $i, X44 : $i]:
% 0.21/0.54         ((k2_zfmisc_1 @ X44 @ (k4_xboole_0 @ X41 @ X43))
% 0.21/0.54           = (k4_xboole_0 @ (k2_zfmisc_1 @ X44 @ X41) @ 
% 0.21/0.54              (k2_zfmisc_1 @ X44 @ X43)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.21/0.54           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('32', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k2_zfmisc_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['27', '33'])).
% 0.21/0.54  thf(t2_boole, axiom,
% 0.21/0.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['26', '34', '35'])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '36'])).
% 0.21/0.54  thf('38', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.54      inference('clc', [status(thm)], ['11', '22'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.54  thf(t62_relat_1, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.54         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( v1_relat_1 @ A ) =>
% 0.21/0.54          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.54            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.21/0.54        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.54      inference('split', [status(esa)], ['41'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X56 : $i, X57 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X56)
% 0.21/0.54          | ~ (v1_relat_1 @ X57)
% 0.21/0.54          | (v1_relat_1 @ (k5_relat_1 @ X56 @ X57)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.54  thf('44', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.54  thf(t46_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( v1_relat_1 @ B ) =>
% 0.21/0.54           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.54             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (![X59 : $i, X60 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X59)
% 0.21/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X60 @ X59)) = (k1_relat_1 @ X60))
% 0.21/0.54          | ~ (r1_tarski @ (k2_relat_1 @ X60) @ (k1_relat_1 @ X59))
% 0.21/0.54          | ~ (v1_relat_1 @ X60))),
% 0.21/0.54      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.54          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.54              = (k1_relat_1 @ k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.54  thf('47', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.54  thf('48', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.54          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.21/0.54  thf('50', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.54      inference('clc', [status(thm)], ['11', '22'])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (![X58 : $i]:
% 0.21/0.54         (((k3_xboole_0 @ X58 @ 
% 0.21/0.54            (k2_zfmisc_1 @ (k1_relat_1 @ X58) @ (k2_relat_1 @ X58))) = (
% 0.21/0.54            X58))
% 0.21/0.54          | ~ (v1_relat_1 @ X58))),
% 0.21/0.54      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k3_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.21/0.54            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.21/0.54             (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.21/0.54            = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['51', '52'])).
% 0.21/0.54  thf('54', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.54         ((k2_zfmisc_1 @ (k4_xboole_0 @ X41 @ X43) @ X42)
% 0.21/0.54           = (k4_xboole_0 @ (k2_zfmisc_1 @ X41 @ X42) @ 
% 0.21/0.54              (k2_zfmisc_1 @ X43 @ X42)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 0.21/0.54           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['55', '56'])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('59', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['54', '60'])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['53', '61', '62'])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['43', '63'])).
% 0.21/0.54  thf('65', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.54      inference('clc', [status(thm)], ['11', '22'])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['64', '65'])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['66'])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.21/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.54      inference('split', [status(esa)], ['41'])).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.21/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.54  thf('70', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('71', plain,
% 0.21/0.54      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.54      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.54  thf('72', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['71'])).
% 0.21/0.54  thf('73', plain,
% 0.21/0.54      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.21/0.54       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('split', [status(esa)], ['41'])).
% 0.21/0.54  thf('74', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['72', '73'])).
% 0.21/0.54  thf('75', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['42', '74'])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['40', '75'])).
% 0.21/0.54  thf('77', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('78', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.54  thf('79', plain, ($false), inference('simplify', [status(thm)], ['78'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
