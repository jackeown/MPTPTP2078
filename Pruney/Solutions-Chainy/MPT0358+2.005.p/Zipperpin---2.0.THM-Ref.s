%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3FaT48Pb0x

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:22 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 298 expanded)
%              Number of leaves         :   33 (  98 expanded)
%              Depth                    :   22
%              Number of atoms          :  864 (2228 expanded)
%              Number of equality atoms :   81 ( 200 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('1',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X24: $i] :
      ( r1_tarski @ k1_xboole_0 @ X24 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X44: $i] :
      ( ( k1_subset_1 @ X44 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('7',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('8',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('12',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('15',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['4','13','14'])).

thf('16',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['2','15'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_xboole_0 @ X31 @ X32 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X31 @ X32 ) @ ( k2_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ X29 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('21',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_xboole_0 @ X31 @ X32 )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ ( k2_xboole_0 @ X31 @ X32 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X30: $i] :
      ( ( k5_xboole_0 @ X30 @ X30 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X23: $i] :
      ( ( k3_xboole_0 @ X23 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X24: $i] :
      ( r1_tarski @ k1_xboole_0 @ X24 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('28',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X33 @ X34 )
      | ( r2_hidden @ X33 @ X35 )
      | ( X35
       != ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('29',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r2_hidden @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( r1_tarski @ X33 @ X34 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('31',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ( m1_subset_1 @ X41 @ X42 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ! [X41: $i,X42: $i] :
      ( ( m1_subset_1 @ X41 @ X42 )
      | ~ ( r2_hidden @ X41 @ X42 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k3_subset_1 @ X45 @ X46 )
        = ( k4_xboole_0 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','36'])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k3_subset_1 @ sk_B_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','36'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X30: $i] :
      ( ( k5_xboole_0 @ X30 @ X30 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('48',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ( r2_hidden @ X5 @ X8 )
      | ( X8
       != ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('49',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['46','50'])).

thf('52',plain,(
    ! [X23: $i] :
      ( ( k3_xboole_0 @ X23 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r2_hidden @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( r1_tarski @ X33 @ X34 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X41: $i,X42: $i] :
      ( ( m1_subset_1 @ X41 @ X42 )
      | ~ ( r2_hidden @ X41 @ X42 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('64',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k3_subset_1 @ X45 @ X46 )
        = ( k4_xboole_0 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k3_subset_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['58','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('69',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ( X8
       != ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('70',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['51','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k3_subset_1 @ X45 @ X46 )
        = ( k4_xboole_0 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('77',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('82',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','82'])).

thf('84',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ( X10
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X7 @ X6 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X10 @ X7 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('85',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('90',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X44: $i] :
      ( ( k1_subset_1 @ X44 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('93',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('94',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','13'])).

thf('96',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['94','95'])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['91','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3FaT48Pb0x
% 0.14/0.33  % Computer   : n014.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 14:35:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 696 iterations in 0.198s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.46/0.64  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(d1_xboole_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.64  thf(t38_subset_1, conjecture,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.64       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.46/0.64         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i]:
% 0.46/0.64        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.64          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.46/0.64            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.46/0.64        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.46/0.64         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.46/0.64      inference('split', [status(esa)], ['1'])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.46/0.64        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.46/0.64       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.46/0.64      inference('split', [status(esa)], ['3'])).
% 0.46/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.64  thf('5', plain, (![X24 : $i]: (r1_tarski @ k1_xboole_0 @ X24)),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.64  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.64  thf('6', plain, (![X44 : $i]: ((k1_subset_1 @ X44) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.46/0.64         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.64      inference('split', [status(esa)], ['1'])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.46/0.64         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.46/0.64      inference('split', [status(esa)], ['3'])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.46/0.64         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.46/0.64             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.46/0.64         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.46/0.64             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.64      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.46/0.64       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '12'])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.46/0.64       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.46/0.64      inference('split', [status(esa)], ['1'])).
% 0.46/0.64  thf('15', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['4', '13', '14'])).
% 0.46/0.64  thf('16', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['2', '15'])).
% 0.46/0.64  thf(t12_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i]:
% 0.46/0.64         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.46/0.64         = (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.64  thf(t95_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k3_xboole_0 @ A @ B ) =
% 0.46/0.64       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X31 : $i, X32 : $i]:
% 0.46/0.64         ((k3_xboole_0 @ X31 @ X32)
% 0.46/0.64           = (k5_xboole_0 @ (k5_xboole_0 @ X31 @ X32) @ 
% 0.46/0.64              (k2_xboole_0 @ X31 @ X32)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.46/0.64  thf(t91_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.64       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ X29)
% 0.46/0.64           = (k5_xboole_0 @ X27 @ (k5_xboole_0 @ X28 @ X29)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X31 : $i, X32 : $i]:
% 0.46/0.64         ((k3_xboole_0 @ X31 @ X32)
% 0.46/0.64           = (k5_xboole_0 @ X31 @ 
% 0.46/0.64              (k5_xboole_0 @ X32 @ (k2_xboole_0 @ X31 @ X32))))),
% 0.46/0.64      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.46/0.64         = (k5_xboole_0 @ sk_B_1 @ 
% 0.46/0.64            (k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ 
% 0.46/0.64             (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['18', '21'])).
% 0.46/0.64  thf(t92_xboole_1, axiom,
% 0.46/0.64    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.64  thf('23', plain, (![X30 : $i]: ((k5_xboole_0 @ X30 @ X30) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.64  thf(t2_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X23 : $i]: ((k3_xboole_0 @ X23 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.64  thf(t100_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X16 : $i, X17 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X16 @ X17)
% 0.46/0.64           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['24', '25'])).
% 0.46/0.64  thf('27', plain, (![X24 : $i]: (r1_tarski @ k1_xboole_0 @ X24)),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.64  thf(d1_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.46/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X33 @ X34)
% 0.46/0.64          | (r2_hidden @ X33 @ X35)
% 0.46/0.64          | ((X35) != (k1_zfmisc_1 @ X34)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X33 : $i, X34 : $i]:
% 0.46/0.64         ((r2_hidden @ X33 @ (k1_zfmisc_1 @ X34)) | ~ (r1_tarski @ X33 @ X34))),
% 0.46/0.64      inference('simplify', [status(thm)], ['28'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['27', '29'])).
% 0.46/0.64  thf(d2_subset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_xboole_0 @ A ) =>
% 0.46/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.46/0.65       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (![X41 : $i, X42 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X41 @ X42)
% 0.46/0.65          | (m1_subset_1 @ X41 @ X42)
% 0.46/0.65          | (v1_xboole_0 @ X42))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X41 : $i, X42 : $i]:
% 0.46/0.65         ((m1_subset_1 @ X41 @ X42) | ~ (r2_hidden @ X41 @ X42))),
% 0.46/0.65      inference('clc', [status(thm)], ['31', '32'])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['30', '33'])).
% 0.46/0.65  thf(d5_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.65       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (![X45 : $i, X46 : $i]:
% 0.46/0.65         (((k3_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))
% 0.46/0.65          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['26', '36'])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.46/0.65         = (k3_subset_1 @ sk_B_1 @ k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['22', '23', '37'])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['26', '36'])).
% 0.46/0.65  thf(t5_boole, axiom,
% 0.46/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.65  thf('40', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 0.46/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.65  thf('41', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['38', '41'])).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X16 @ X17)
% 0.46/0.65           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.46/0.65         = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['42', '43'])).
% 0.46/0.65  thf('45', plain, (![X30 : $i]: ((k5_xboole_0 @ X30 @ X30) = (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['44', '45'])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.65  thf(d5_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.46/0.65       ( ![D:$i]:
% 0.46/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.65           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X5 @ X6)
% 0.46/0.65          | (r2_hidden @ X5 @ X7)
% 0.46/0.65          | (r2_hidden @ X5 @ X8)
% 0.46/0.65          | ((X8) != (k4_xboole_0 @ X6 @ X7)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.65         ((r2_hidden @ X5 @ (k4_xboole_0 @ X6 @ X7))
% 0.46/0.65          | (r2_hidden @ X5 @ X7)
% 0.46/0.65          | ~ (r2_hidden @ X5 @ X6))),
% 0.46/0.65      inference('simplify', [status(thm)], ['48'])).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X0)
% 0.46/0.65          | (r2_hidden @ (sk_B @ X0) @ X1)
% 0.46/0.65          | (r2_hidden @ (sk_B @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['47', '49'])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (((r2_hidden @ (sk_B @ sk_B_1) @ k1_xboole_0)
% 0.46/0.65        | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['46', '50'])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (![X23 : $i]: ((k3_xboole_0 @ X23 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.65  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X16 @ X17)
% 0.46/0.65           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.65           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['54', '55'])).
% 0.46/0.65  thf('57', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 0.46/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['56', '57'])).
% 0.46/0.65  thf(d10_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.65  thf('60', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.46/0.65      inference('simplify', [status(thm)], ['59'])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      (![X33 : $i, X34 : $i]:
% 0.46/0.65         ((r2_hidden @ X33 @ (k1_zfmisc_1 @ X34)) | ~ (r1_tarski @ X33 @ X34))),
% 0.46/0.65      inference('simplify', [status(thm)], ['28'])).
% 0.46/0.65  thf('62', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      (![X41 : $i, X42 : $i]:
% 0.46/0.65         ((m1_subset_1 @ X41 @ X42) | ~ (r2_hidden @ X41 @ X42))),
% 0.46/0.65      inference('clc', [status(thm)], ['31', '32'])).
% 0.46/0.65  thf('64', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      (![X45 : $i, X46 : $i]:
% 0.46/0.65         (((k3_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))
% 0.46/0.65          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['64', '65'])).
% 0.46/0.65  thf('67', plain,
% 0.46/0.65      (((k3_subset_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['58', '66'])).
% 0.46/0.65  thf('68', plain,
% 0.46/0.65      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['64', '65'])).
% 0.46/0.65  thf('69', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X9 @ X8)
% 0.46/0.65          | ~ (r2_hidden @ X9 @ X7)
% 0.46/0.65          | ((X8) != (k4_xboole_0 @ X6 @ X7)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.65  thf('70', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X9 @ X7)
% 0.46/0.65          | ~ (r2_hidden @ X9 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['69'])).
% 0.46/0.65  thf('71', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ X0))
% 0.46/0.65          | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['68', '70'])).
% 0.46/0.65  thf('72', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['67', '71'])).
% 0.46/0.65  thf('73', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.65      inference('simplify', [status(thm)], ['72'])).
% 0.46/0.65  thf('74', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.46/0.65      inference('clc', [status(thm)], ['51', '73'])).
% 0.46/0.65  thf('75', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('76', plain,
% 0.46/0.65      (![X45 : $i, X46 : $i]:
% 0.46/0.65         (((k3_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))
% 0.46/0.65          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.65  thf('77', plain,
% 0.46/0.65      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['75', '76'])).
% 0.46/0.65  thf('78', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X9 @ X7)
% 0.46/0.65          | ~ (r2_hidden @ X9 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['69'])).
% 0.46/0.65  thf('79', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.46/0.65          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['77', '78'])).
% 0.46/0.65  thf('80', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_B_1) | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['74', '79'])).
% 0.46/0.65  thf('81', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.65  thf('82', plain, (~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.46/0.65      inference('clc', [status(thm)], ['80', '81'])).
% 0.46/0.65  thf('83', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.46/0.65      inference('sup-', [status(thm)], ['0', '82'])).
% 0.46/0.65  thf('84', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i, X10 : $i]:
% 0.46/0.65         (((X10) = (k4_xboole_0 @ X6 @ X7))
% 0.46/0.65          | (r2_hidden @ (sk_D @ X10 @ X7 @ X6) @ X6)
% 0.46/0.65          | (r2_hidden @ (sk_D @ X10 @ X7 @ X6) @ X10))),
% 0.46/0.65      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.65  thf('85', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.65  thf('86', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X1)
% 0.46/0.65          | ((X0) = (k4_xboole_0 @ X1 @ X2))
% 0.46/0.65          | ~ (v1_xboole_0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['84', '85'])).
% 0.46/0.65  thf('87', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.65      inference('simplify', [status(thm)], ['72'])).
% 0.46/0.65  thf('88', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (v1_xboole_0 @ X1) | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['86', '87'])).
% 0.46/0.65  thf('89', plain,
% 0.46/0.65      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['56', '57'])).
% 0.46/0.65  thf('90', plain,
% 0.46/0.65      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ((X1) = (k1_xboole_0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['88', '89'])).
% 0.46/0.65  thf('91', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['83', '90'])).
% 0.46/0.65  thf('92', plain, (![X44 : $i]: ((k1_subset_1 @ X44) = (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.46/0.65  thf('93', plain,
% 0.46/0.65      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.46/0.65         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.65      inference('split', [status(esa)], ['3'])).
% 0.46/0.65  thf('94', plain,
% 0.46/0.65      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['92', '93'])).
% 0.46/0.65  thf('95', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['4', '13'])).
% 0.46/0.65  thf('96', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['94', '95'])).
% 0.46/0.65  thf('97', plain, ($false),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['91', '96'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
