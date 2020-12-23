%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w2Fglo3J2p

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:47 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 552 expanded)
%              Number of leaves         :   37 ( 192 expanded)
%              Depth                    :   27
%              Number of atoms          :  969 (4104 expanded)
%              Number of equality atoms :   93 ( 418 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ X60 )
      | ( r2_hidden @ X59 @ X60 )
      | ( v1_xboole_0 @ X60 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X65: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( r2_hidden @ X55 @ X54 )
      | ( r1_tarski @ X55 @ X53 )
      | ( X54
       != ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X53: $i,X55: $i] :
      ( ( r1_tarski @ X55 @ X53 )
      | ~ ( r2_hidden @ X55 @ ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k5_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r1_tarski @ X52 @ X53 )
      | ( r2_hidden @ X52 @ X54 )
      | ( X54
       != ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('14',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r2_hidden @ X52 @ ( k1_zfmisc_1 @ X53 ) )
      | ~ ( r1_tarski @ X52 @ X53 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    r2_hidden @ ( k5_xboole_0 @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( r2_hidden @ X59 @ X60 )
      | ( m1_subset_1 @ X59 @ X60 )
      | ( v1_xboole_0 @ X60 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X59: $i,X60: $i] :
      ( ( m1_subset_1 @ X59 @ X60 )
      | ~ ( r2_hidden @ X59 @ X60 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X63: $i,X64: $i] :
      ( ( ( k3_subset_1 @ X63 @ X64 )
        = ( k4_xboole_0 @ X63 @ X64 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('22',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('30',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('31',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k5_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k5_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X57 @ X58 ) )
      = ( k2_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X57 @ X58 ) )
      = ( k2_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('51',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('52',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('53',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('55',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('56',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50','51','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('61',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('65',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('68',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['66','75','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','79'])).

thf('81',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','78'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['22','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('87',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['6','8'])).

thf('88',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('89',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['85','86','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','78'])).

thf('92',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('95',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ X67 ) )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ X67 ) )
      | ( ( k4_subset_1 @ X67 @ X66 @ X68 )
        = ( k2_xboole_0 @ X66 @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('99',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('100',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['87','88'])).

thf('102',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['97','102'])).

thf('104',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('105',plain,(
    ! [X62: $i] :
      ( ( k2_subset_1 @ X62 )
      = X62 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('106',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
 != sk_A ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['103','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w2Fglo3J2p
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 363 iterations in 0.116s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.38/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.56  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.38/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(d10_xboole_0, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.56  thf('1', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.38/0.56      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.56  thf(t25_subset_1, conjecture,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.56       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.38/0.56         ( k2_subset_1 @ A ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i]:
% 0.38/0.56        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.56          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.38/0.56            ( k2_subset_1 @ A ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.38/0.56  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d2_subset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( v1_xboole_0 @ A ) =>
% 0.38/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.38/0.56       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (![X59 : $i, X60 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X59 @ X60)
% 0.38/0.56          | (r2_hidden @ X59 @ X60)
% 0.38/0.56          | (v1_xboole_0 @ X60))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.38/0.56        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf(fc1_subset_1, axiom,
% 0.38/0.56    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.56  thf('5', plain, (![X65 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X65))),
% 0.38/0.56      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.38/0.56  thf('6', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.56      inference('clc', [status(thm)], ['4', '5'])).
% 0.38/0.56  thf(d1_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.38/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X55 @ X54)
% 0.38/0.56          | (r1_tarski @ X55 @ X53)
% 0.38/0.56          | ((X54) != (k1_zfmisc_1 @ X53)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (![X53 : $i, X55 : $i]:
% 0.38/0.56         ((r1_tarski @ X55 @ X53) | ~ (r2_hidden @ X55 @ (k1_zfmisc_1 @ X53)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.38/0.56  thf('9', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['6', '8'])).
% 0.38/0.56  thf(t110_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.38/0.56       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.56         (~ (r1_tarski @ X10 @ X11)
% 0.38/0.56          | ~ (r1_tarski @ X12 @ X11)
% 0.38/0.56          | (r1_tarski @ (k5_xboole_0 @ X10 @ X12) @ X11))),
% 0.38/0.56      inference('cnf', [status(esa)], [t110_xboole_1])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r1_tarski @ (k5_xboole_0 @ sk_B_1 @ X0) @ sk_A)
% 0.38/0.56          | ~ (r1_tarski @ X0 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.56  thf('12', plain, ((r1_tarski @ (k5_xboole_0 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '11'])).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.38/0.56         (~ (r1_tarski @ X52 @ X53)
% 0.38/0.56          | (r2_hidden @ X52 @ X54)
% 0.38/0.56          | ((X54) != (k1_zfmisc_1 @ X53)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (![X52 : $i, X53 : $i]:
% 0.38/0.56         ((r2_hidden @ X52 @ (k1_zfmisc_1 @ X53)) | ~ (r1_tarski @ X52 @ X53))),
% 0.38/0.56      inference('simplify', [status(thm)], ['13'])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      ((r2_hidden @ (k5_xboole_0 @ sk_B_1 @ sk_A) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['12', '14'])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      (![X59 : $i, X60 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X59 @ X60)
% 0.38/0.56          | (m1_subset_1 @ X59 @ X60)
% 0.38/0.56          | (v1_xboole_0 @ X60))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.38/0.56  thf(d1_xboole_0, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X59 : $i, X60 : $i]:
% 0.38/0.56         ((m1_subset_1 @ X59 @ X60) | ~ (r2_hidden @ X59 @ X60))),
% 0.38/0.56      inference('clc', [status(thm)], ['16', '17'])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      ((m1_subset_1 @ (k5_xboole_0 @ sk_B_1 @ sk_A) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['15', '18'])).
% 0.38/0.56  thf('20', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d5_subset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.56       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (![X63 : $i, X64 : $i]:
% 0.38/0.56         (((k3_subset_1 @ X63 @ X64) = (k4_xboole_0 @ X63 @ X64))
% 0.38/0.56          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X63)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.56  thf(t95_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( k3_xboole_0 @ A @ B ) =
% 0.38/0.56       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (![X21 : $i, X22 : $i]:
% 0.38/0.56         ((k3_xboole_0 @ X21 @ X22)
% 0.38/0.56           = (k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ 
% 0.38/0.56              (k2_xboole_0 @ X21 @ X22)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.38/0.56  thf(t91_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.38/0.56       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.38/0.56           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      (![X21 : $i, X22 : $i]:
% 0.38/0.56         ((k3_xboole_0 @ X21 @ X22)
% 0.38/0.56           = (k5_xboole_0 @ X21 @ 
% 0.38/0.56              (k5_xboole_0 @ X22 @ (k2_xboole_0 @ X21 @ X22))))),
% 0.38/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.38/0.56  thf(t92_xboole_1, axiom,
% 0.38/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.38/0.56  thf('26', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.38/0.56           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['26', '27'])).
% 0.38/0.56  thf('29', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.38/0.56      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.56  thf('30', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.38/0.56      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.56  thf('31', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.38/0.56      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.56         (~ (r1_tarski @ X10 @ X11)
% 0.38/0.56          | ~ (r1_tarski @ X12 @ X11)
% 0.38/0.56          | (r1_tarski @ (k5_xboole_0 @ X10 @ X12) @ X11))),
% 0.38/0.56      inference('cnf', [status(esa)], [t110_xboole_1])).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((r1_tarski @ (k5_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.56  thf('34', plain, (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X0)),
% 0.38/0.56      inference('sup-', [status(thm)], ['30', '33'])).
% 0.38/0.56  thf('35', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.56  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.56         (~ (r1_tarski @ X10 @ X11)
% 0.38/0.56          | ~ (r1_tarski @ X12 @ X11)
% 0.38/0.56          | (r1_tarski @ (k5_xboole_0 @ X10 @ X12) @ X11))),
% 0.38/0.56      inference('cnf', [status(esa)], [t110_xboole_1])).
% 0.38/0.56  thf('38', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((r1_tarski @ (k5_xboole_0 @ k1_xboole_0 @ X1) @ X0)
% 0.38/0.56          | ~ (r1_tarski @ X1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.56  thf('39', plain,
% 0.38/0.56      (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 0.38/0.56      inference('sup-', [status(thm)], ['29', '38'])).
% 0.38/0.56  thf(t12_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      (![X13 : $i, X14 : $i]:
% 0.38/0.56         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.38/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.56  thf('41', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k2_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.56  thf(commutativity_k2_tarski, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.38/0.56  thf('42', plain,
% 0.38/0.56      (![X23 : $i, X24 : $i]:
% 0.38/0.56         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 0.38/0.56      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.38/0.56  thf(l51_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      (![X57 : $i, X58 : $i]:
% 0.38/0.56         ((k3_tarski @ (k2_tarski @ X57 @ X58)) = (k2_xboole_0 @ X57 @ X58))),
% 0.38/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.56      inference('sup+', [status(thm)], ['42', '43'])).
% 0.38/0.56  thf('45', plain,
% 0.38/0.56      (![X57 : $i, X58 : $i]:
% 0.38/0.56         ((k3_tarski @ (k2_tarski @ X57 @ X58)) = (k2_xboole_0 @ X57 @ X58))),
% 0.38/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.56  thf('46', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.56      inference('sup+', [status(thm)], ['44', '45'])).
% 0.38/0.56  thf('47', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)) = (X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['41', '46'])).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      (![X21 : $i, X22 : $i]:
% 0.38/0.56         ((k3_xboole_0 @ X21 @ X22)
% 0.38/0.56           = (k5_xboole_0 @ X21 @ 
% 0.38/0.56              (k5_xboole_0 @ X22 @ (k2_xboole_0 @ X21 @ X22))))),
% 0.38/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.38/0.56  thf('49', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0))
% 0.38/0.56           = (k5_xboole_0 @ X0 @ 
% 0.38/0.56              (k5_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['47', '48'])).
% 0.38/0.56  thf('50', plain,
% 0.38/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.38/0.56           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.38/0.56  thf('51', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.56  thf(idempotence_k2_xboole_0, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.38/0.56  thf('52', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ X3) = (X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.38/0.56  thf('53', plain,
% 0.38/0.56      (![X21 : $i, X22 : $i]:
% 0.38/0.56         ((k3_xboole_0 @ X21 @ X22)
% 0.38/0.56           = (k5_xboole_0 @ X21 @ 
% 0.38/0.56              (k5_xboole_0 @ X22 @ (k2_xboole_0 @ X21 @ X22))))),
% 0.38/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.38/0.56  thf('54', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k3_xboole_0 @ X0 @ X0)
% 0.38/0.56           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['52', '53'])).
% 0.38/0.56  thf(idempotence_k3_xboole_0, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.38/0.56  thf('55', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.38/0.56      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.38/0.56  thf('56', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.56  thf('57', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.38/0.56  thf('58', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0))
% 0.38/0.56           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['49', '50', '51', '57'])).
% 0.38/0.56  thf('59', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.38/0.56  thf('60', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)) = (X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['58', '59'])).
% 0.38/0.56  thf(t100_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.56  thf('61', plain,
% 0.38/0.56      (![X8 : $i, X9 : $i]:
% 0.38/0.56         ((k4_xboole_0 @ X8 @ X9)
% 0.38/0.56           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.56  thf('62', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0))
% 0.38/0.56           = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['60', '61'])).
% 0.38/0.56  thf('63', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.56  thf('64', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['62', '63'])).
% 0.38/0.56  thf(t39_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.56  thf('65', plain,
% 0.38/0.56      (![X15 : $i, X16 : $i]:
% 0.38/0.56         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 0.38/0.56           = (k2_xboole_0 @ X15 @ X16))),
% 0.38/0.56      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.56  thf('66', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k2_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.38/0.56           = (k2_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['64', '65'])).
% 0.38/0.56  thf('67', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.38/0.56      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.38/0.56  thf('68', plain,
% 0.38/0.56      (![X8 : $i, X9 : $i]:
% 0.38/0.56         ((k4_xboole_0 @ X8 @ X9)
% 0.38/0.56           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.56  thf('69', plain,
% 0.38/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['67', '68'])).
% 0.38/0.56  thf('70', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.56  thf('71', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['69', '70'])).
% 0.38/0.56  thf('72', plain,
% 0.38/0.56      (![X15 : $i, X16 : $i]:
% 0.38/0.56         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 0.38/0.56           = (k2_xboole_0 @ X15 @ X16))),
% 0.38/0.56      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.56  thf('73', plain,
% 0.38/0.56      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['71', '72'])).
% 0.38/0.56  thf('74', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ X3) = (X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.38/0.56  thf('75', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['73', '74'])).
% 0.38/0.56  thf('76', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.56      inference('sup+', [status(thm)], ['44', '45'])).
% 0.38/0.56  thf('77', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)) = (X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['41', '46'])).
% 0.38/0.56  thf('78', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['66', '75', '76', '77'])).
% 0.38/0.56  thf('79', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['28', '78'])).
% 0.38/0.56  thf('80', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.38/0.56           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['25', '79'])).
% 0.38/0.56  thf('81', plain,
% 0.38/0.56      (![X8 : $i, X9 : $i]:
% 0.38/0.56         ((k4_xboole_0 @ X8 @ X9)
% 0.38/0.56           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.56  thf('82', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.38/0.56           = (k4_xboole_0 @ X1 @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['80', '81'])).
% 0.38/0.56  thf('83', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['28', '78'])).
% 0.38/0.56  thf('84', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k2_xboole_0 @ X1 @ X0)
% 0.38/0.56           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['82', '83'])).
% 0.38/0.56  thf('85', plain,
% 0.38/0.56      (((k2_xboole_0 @ sk_A @ sk_B_1)
% 0.38/0.56         = (k5_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['22', '84'])).
% 0.38/0.56  thf('86', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.56      inference('sup+', [status(thm)], ['44', '45'])).
% 0.38/0.56  thf('87', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['6', '8'])).
% 0.38/0.56  thf('88', plain,
% 0.38/0.56      (![X13 : $i, X14 : $i]:
% 0.38/0.56         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.38/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.56  thf('89', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['87', '88'])).
% 0.38/0.56  thf('90', plain,
% 0.38/0.56      (((sk_A) = (k5_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['85', '86', '89'])).
% 0.38/0.56  thf('91', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['28', '78'])).
% 0.38/0.56  thf('92', plain,
% 0.38/0.56      (((k3_subset_1 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_B_1 @ sk_A))),
% 0.38/0.56      inference('sup+', [status(thm)], ['90', '91'])).
% 0.38/0.56  thf('93', plain,
% 0.38/0.56      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['19', '92'])).
% 0.38/0.56  thf('94', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(redefinition_k4_subset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.38/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.56       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.38/0.56  thf('95', plain,
% 0.38/0.56      (![X66 : $i, X67 : $i, X68 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ X67))
% 0.38/0.56          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ X67))
% 0.38/0.56          | ((k4_subset_1 @ X67 @ X66 @ X68) = (k2_xboole_0 @ X66 @ X68)))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.38/0.56  thf('96', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k4_subset_1 @ sk_A @ sk_B_1 @ X0) = (k2_xboole_0 @ sk_B_1 @ X0))
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['94', '95'])).
% 0.38/0.56  thf('97', plain,
% 0.38/0.56      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.38/0.56         = (k2_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['93', '96'])).
% 0.38/0.56  thf('98', plain,
% 0.38/0.56      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.56  thf('99', plain,
% 0.38/0.56      (![X15 : $i, X16 : $i]:
% 0.38/0.56         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 0.38/0.56           = (k2_xboole_0 @ X15 @ X16))),
% 0.38/0.56      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.56  thf('100', plain,
% 0.38/0.56      (((k2_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.38/0.56         = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.38/0.56      inference('sup+', [status(thm)], ['98', '99'])).
% 0.38/0.56  thf('101', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['87', '88'])).
% 0.38/0.56  thf('102', plain,
% 0.38/0.56      (((k2_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['100', '101'])).
% 0.38/0.56  thf('103', plain,
% 0.38/0.56      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['97', '102'])).
% 0.38/0.56  thf('104', plain,
% 0.38/0.56      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.38/0.56         != (k2_subset_1 @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.38/0.56  thf('105', plain, (![X62 : $i]: ((k2_subset_1 @ X62) = (X62))),
% 0.38/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.38/0.56  thf('106', plain,
% 0.38/0.56      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) != (sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['104', '105'])).
% 0.38/0.56  thf('107', plain, ($false),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['103', '106'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
