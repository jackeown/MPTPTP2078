%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5JAge39M2D

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 171 expanded)
%              Number of leaves         :   31 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  641 (1224 expanded)
%              Number of equality atoms :   79 ( 161 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ~ ( v1_relat_1 @ X52 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X51 @ X52 ) ) ) ),
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
    ! [X56: $i,X57: $i] :
      ( ~ ( v1_relat_1 @ X56 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X56 @ X57 ) )
        = ( k2_relat_1 @ X57 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X57 ) @ ( k2_relat_1 @ X56 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
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
    ! [X48: $i] :
      ( ( v1_relat_1 @ X48 )
      | ( r2_hidden @ ( sk_B @ X48 ) @ X48 ) ) ),
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
    ! [X41: $i,X42: $i] :
      ( ( X42 != X41 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X42 ) @ ( k1_tarski @ X41 ) )
       != ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('13',plain,(
    ! [X41: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X41 ) @ ( k1_tarski @ X41 ) )
     != ( k1_tarski @ X41 ) ) ),
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
    ! [X41: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X41 ) ) ),
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
    ! [X53: $i] :
      ( ( ( k3_xboole_0 @ X53 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X53 ) @ ( k2_relat_1 @ X53 ) ) )
        = X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k2_zfmisc_1 @ X39 @ X40 )
        = k1_xboole_0 )
      | ( X40 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('24',plain,(
    ! [X39: $i] :
      ( ( k2_zfmisc_1 @ X39 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['22','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['11','18'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

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

thf('31',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ~ ( v1_relat_1 @ X52 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X51 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('34',plain,
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

thf('35',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v1_relat_1 @ X54 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X55 @ X54 ) )
        = ( k1_relat_1 @ X55 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X55 ) @ ( k1_relat_1 @ X54 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('38',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['11','18'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X53: $i] :
      ( ( ( k3_xboole_0 @ X53 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X53 ) @ ( k2_relat_1 @ X53 ) ) )
        = X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k2_zfmisc_1 @ X39 @ X40 )
        = k1_xboole_0 )
      | ( X39 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X40: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X40 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','47'])).

thf('49',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['11','18'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('53',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('58',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['32','58'])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference(simplify,[status(thm)],['62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5JAge39M2D
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:18:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 241 iterations in 0.081s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(dt_k5_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.22/0.54       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.22/0.54  thf('0', plain,
% 0.22/0.54      (![X51 : $i, X52 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X51)
% 0.22/0.54          | ~ (v1_relat_1 @ X52)
% 0.22/0.54          | (v1_relat_1 @ (k5_relat_1 @ X51 @ X52)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.22/0.54  thf(t60_relat_1, axiom,
% 0.22/0.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.54  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.54  thf(t47_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( v1_relat_1 @ B ) =>
% 0.22/0.54           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.22/0.54             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X56 : $i, X57 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X56)
% 0.22/0.54          | ((k2_relat_1 @ (k5_relat_1 @ X56 @ X57)) = (k2_relat_1 @ X57))
% 0.22/0.54          | ~ (r1_tarski @ (k1_relat_1 @ X57) @ (k2_relat_1 @ X56))
% 0.22/0.54          | ~ (v1_relat_1 @ X57))),
% 0.22/0.54      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.54          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.54              = (k2_relat_1 @ k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.54  thf('4', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.54  thf('5', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.54          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.22/0.54  thf(d1_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) <=>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.54              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (![X48 : $i]: ((v1_relat_1 @ X48) | (r2_hidden @ (sk_B @ X48) @ X48))),
% 0.22/0.54      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.22/0.54  thf(l1_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X35 : $i, X37 : $i]:
% 0.22/0.54         ((r1_tarski @ (k1_tarski @ X35) @ X37) | ~ (r2_hidden @ X35 @ X37))),
% 0.22/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v1_relat_1 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.54  thf(t3_xboole_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (((v1_relat_1 @ k1_xboole_0)
% 0.22/0.54        | ((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.54  thf(t20_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.54         ( k1_tarski @ A ) ) <=>
% 0.22/0.54       ( ( A ) != ( B ) ) ))).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (![X41 : $i, X42 : $i]:
% 0.22/0.54         (((X42) != (X41))
% 0.22/0.54          | ((k4_xboole_0 @ (k1_tarski @ X42) @ (k1_tarski @ X41))
% 0.22/0.54              != (k1_tarski @ X42)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (![X41 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ (k1_tarski @ X41) @ (k1_tarski @ X41))
% 0.22/0.54           != (k1_tarski @ X41))),
% 0.22/0.54      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.54  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.54  thf('14', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.54      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.54  thf(t100_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (![X1 : $i, X2 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X1 @ X2)
% 0.22/0.54           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.54  thf(t92_xboole_1, axiom,
% 0.22/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.54  thf('17', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.54  thf('18', plain, (![X41 : $i]: ((k1_xboole_0) != (k1_tarski @ X41))),
% 0.22/0.54      inference('demod', [status(thm)], ['13', '16', '17'])).
% 0.22/0.54  thf('19', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.54      inference('clc', [status(thm)], ['11', '18'])).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['6', '19'])).
% 0.22/0.54  thf(t22_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ( k3_xboole_0 @
% 0.22/0.54           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.22/0.54         ( A ) ) ))).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X53 : $i]:
% 0.22/0.54         (((k3_xboole_0 @ X53 @ 
% 0.22/0.54            (k2_zfmisc_1 @ (k1_relat_1 @ X53) @ (k2_relat_1 @ X53))) = (
% 0.22/0.54            X53))
% 0.22/0.54          | ~ (v1_relat_1 @ X53))),
% 0.22/0.54      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k3_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.22/0.54            (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.22/0.54             k1_xboole_0))
% 0.22/0.54            = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.54  thf(t113_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X39 : $i, X40 : $i]:
% 0.22/0.54         (((k2_zfmisc_1 @ X39 @ X40) = (k1_xboole_0))
% 0.22/0.54          | ((X40) != (k1_xboole_0)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      (![X39 : $i]: ((k2_zfmisc_1 @ X39 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.54  thf(t2_boole, axiom,
% 0.22/0.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['22', '24', '25'])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['0', '26'])).
% 0.22/0.54  thf('28', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.54      inference('clc', [status(thm)], ['11', '18'])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.54  thf(t62_relat_1, conjecture,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.22/0.54         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]:
% 0.22/0.54        ( ( v1_relat_1 @ A ) =>
% 0.22/0.54          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.22/0.54            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.22/0.54        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.54      inference('split', [status(esa)], ['31'])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      (![X51 : $i, X52 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X51)
% 0.22/0.54          | ~ (v1_relat_1 @ X52)
% 0.22/0.54          | (v1_relat_1 @ (k5_relat_1 @ X51 @ X52)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.22/0.54  thf('34', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.54  thf(t46_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( v1_relat_1 @ B ) =>
% 0.22/0.54           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.54             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (![X54 : $i, X55 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X54)
% 0.22/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X55 @ X54)) = (k1_relat_1 @ X55))
% 0.22/0.54          | ~ (r1_tarski @ (k2_relat_1 @ X55) @ (k1_relat_1 @ X54))
% 0.22/0.54          | ~ (v1_relat_1 @ X55))),
% 0.22/0.54      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.54          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.54              = (k1_relat_1 @ k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.54  thf('37', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.54  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.54  thf('39', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.54          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.22/0.54  thf('40', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.54      inference('clc', [status(thm)], ['11', '18'])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      (![X53 : $i]:
% 0.22/0.54         (((k3_xboole_0 @ X53 @ 
% 0.22/0.54            (k2_zfmisc_1 @ (k1_relat_1 @ X53) @ (k2_relat_1 @ X53))) = (
% 0.22/0.54            X53))
% 0.22/0.54          | ~ (v1_relat_1 @ X53))),
% 0.22/0.54      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.22/0.54  thf('43', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k3_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.22/0.54            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.22/0.54             (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.22/0.54            = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['41', '42'])).
% 0.22/0.54  thf('44', plain,
% 0.22/0.54      (![X39 : $i, X40 : $i]:
% 0.22/0.54         (((k2_zfmisc_1 @ X39 @ X40) = (k1_xboole_0))
% 0.22/0.54          | ((X39) != (k1_xboole_0)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.54  thf('45', plain,
% 0.22/0.54      (![X40 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X40) = (k1_xboole_0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['44'])).
% 0.22/0.54  thf('46', plain,
% 0.22/0.54      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.54  thf('47', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['43', '45', '46'])).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['33', '47'])).
% 0.22/0.54  thf('49', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.54      inference('clc', [status(thm)], ['11', '18'])).
% 0.22/0.54  thf('50', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.54  thf('51', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['50'])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.22/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('split', [status(esa)], ['31'])).
% 0.22/0.54  thf('53', plain,
% 0.22/0.54      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.22/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.54  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('55', plain,
% 0.22/0.54      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.22/0.54  thf('56', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['55'])).
% 0.22/0.54  thf('57', plain,
% 0.22/0.54      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.22/0.54       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.54      inference('split', [status(esa)], ['31'])).
% 0.22/0.54  thf('58', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 0.22/0.54  thf('59', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['32', '58'])).
% 0.22/0.54  thf('60', plain,
% 0.22/0.54      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['30', '59'])).
% 0.22/0.54  thf('61', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('62', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['60', '61'])).
% 0.22/0.54  thf('63', plain, ($false), inference('simplify', [status(thm)], ['62'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
