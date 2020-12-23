%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZrAjsgmvl2

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:53 EST 2020

% Result     : Theorem 10.39s
% Output     : Refutation 10.39s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 930 expanded)
%              Number of leaves         :   39 ( 310 expanded)
%              Depth                    :   19
%              Number of atoms          : 1421 (7371 expanded)
%              Number of equality atoms :  136 ( 686 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

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

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X67: $i,X68: $i] :
      ( ( ( k3_subset_1 @ X67 @ X68 )
        = ( k4_xboole_0 @ X67 @ X68 ) )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ X64 )
      | ( r2_hidden @ X63 @ X64 )
      | ( v1_xboole_0 @ X64 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X69: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('8',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('9',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( r2_hidden @ X59 @ X58 )
      | ( r1_tarski @ X59 @ X57 )
      | ( X58
       != ( k1_zfmisc_1 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('10',plain,(
    ! [X57: $i,X59: $i] :
      ( ( r1_tarski @ X59 @ X57 )
      | ~ ( r2_hidden @ X59 @ ( k1_zfmisc_1 @ X57 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['8','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['3','15'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['16','25'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['0','32'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('34',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('42',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['0','32'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('51',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) )
      = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['46','55'])).

thf('57',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('58',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('59',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( r1_tarski @ X56 @ X57 )
      | ( r2_hidden @ X56 @ X58 )
      | ( X58
       != ( k1_zfmisc_1 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('60',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r2_hidden @ X56 @ ( k1_zfmisc_1 @ X57 ) )
      | ~ ( r1_tarski @ X56 @ X57 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( r2_hidden @ X63 @ X64 )
      | ( m1_subset_1 @ X63 @ X64 )
      | ( v1_xboole_0 @ X64 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X69: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('68',plain,(
    ! [X70: $i,X71: $i,X72: $i] :
      ( ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ X71 ) )
      | ~ ( m1_subset_1 @ X72 @ ( k1_zfmisc_1 @ X71 ) )
      | ( ( k4_subset_1 @ X71 @ X70 @ X72 )
        = ( k2_xboole_0 @ X70 @ X72 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('69',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('70',plain,(
    ! [X70: $i,X71: $i,X72: $i] :
      ( ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ X71 ) )
      | ~ ( m1_subset_1 @ X72 @ ( k1_zfmisc_1 @ X71 ) )
      | ( ( k4_subset_1 @ X71 @ X70 @ X72 )
        = ( k3_tarski @ ( k2_tarski @ X70 @ X72 ) ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['56','72'])).

thf('74',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('75',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('76',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('78',plain,
    ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('80',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('82',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('83',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('84',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('89',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
      = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('92',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('93',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['74','75'])).

thf('95',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r2_hidden @ X56 @ ( k1_zfmisc_1 @ X57 ) )
      | ~ ( r1_tarski @ X56 @ X57 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('96',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( r2_hidden @ X63 @ X64 )
      | ( m1_subset_1 @ X63 @ X64 )
      | ( v1_xboole_0 @ X64 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X69: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('100',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X67: $i,X68: $i] :
      ( ( ( k3_subset_1 @ X67 @ X68 )
        = ( k4_xboole_0 @ X67 @ X68 ) )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('102',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','102'])).

thf('104',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('105',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('106',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('108',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('110',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('112',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','112'])).

thf('114',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('115',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('118',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['113','122'])).

thf('124',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('125',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
      = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['90','125'])).

thf('127',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['82','126'])).

thf('128',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('129',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('131',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['127','128','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('134',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('135',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('136',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','80','81','132','133','134','135'])).

thf('137',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['127','128','131'])).

thf('138',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('140',plain,(
    ! [X66: $i] :
      ( ( k2_subset_1 @ X66 )
      = X66 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('141',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['138','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZrAjsgmvl2
% 0.15/0.37  % Computer   : n020.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 14:14:22 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.22/0.38  % Python version: Python 3.6.8
% 0.22/0.38  % Running in FO mode
% 10.39/10.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.39/10.61  % Solved by: fo/fo7.sh
% 10.39/10.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.39/10.61  % done 9416 iterations in 10.121s
% 10.39/10.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.39/10.61  % SZS output start Refutation
% 10.39/10.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 10.39/10.61  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 10.39/10.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 10.39/10.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.39/10.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 10.39/10.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 10.39/10.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 10.39/10.61  thf(sk_A_type, type, sk_A: $i).
% 10.39/10.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.39/10.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.39/10.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.39/10.61  thf(sk_B_type, type, sk_B: $i).
% 10.39/10.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 10.39/10.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.39/10.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 10.39/10.61  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 10.39/10.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 10.39/10.61  thf(commutativity_k3_xboole_0, axiom,
% 10.39/10.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 10.39/10.61  thf('0', plain,
% 10.39/10.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 10.39/10.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 10.39/10.61  thf(t25_subset_1, conjecture,
% 10.39/10.61    (![A:$i,B:$i]:
% 10.39/10.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.39/10.61       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 10.39/10.61         ( k2_subset_1 @ A ) ) ))).
% 10.39/10.61  thf(zf_stmt_0, negated_conjecture,
% 10.39/10.61    (~( ![A:$i,B:$i]:
% 10.39/10.61        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.39/10.61          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 10.39/10.61            ( k2_subset_1 @ A ) ) ) )),
% 10.39/10.61    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 10.39/10.61  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 10.39/10.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.39/10.61  thf(d5_subset_1, axiom,
% 10.39/10.61    (![A:$i,B:$i]:
% 10.39/10.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.39/10.61       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 10.39/10.61  thf('2', plain,
% 10.39/10.61      (![X67 : $i, X68 : $i]:
% 10.39/10.61         (((k3_subset_1 @ X67 @ X68) = (k4_xboole_0 @ X67 @ X68))
% 10.39/10.61          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ X67)))),
% 10.39/10.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 10.39/10.61  thf('3', plain,
% 10.39/10.61      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 10.39/10.61      inference('sup-', [status(thm)], ['1', '2'])).
% 10.39/10.61  thf('4', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 10.39/10.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.39/10.61  thf(d2_subset_1, axiom,
% 10.39/10.61    (![A:$i,B:$i]:
% 10.39/10.61     ( ( ( v1_xboole_0 @ A ) =>
% 10.39/10.61         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 10.39/10.61       ( ( ~( v1_xboole_0 @ A ) ) =>
% 10.39/10.61         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 10.39/10.61  thf('5', plain,
% 10.39/10.61      (![X63 : $i, X64 : $i]:
% 10.39/10.61         (~ (m1_subset_1 @ X63 @ X64)
% 10.39/10.61          | (r2_hidden @ X63 @ X64)
% 10.39/10.61          | (v1_xboole_0 @ X64))),
% 10.39/10.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 10.39/10.61  thf('6', plain,
% 10.39/10.61      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 10.39/10.61        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 10.39/10.61      inference('sup-', [status(thm)], ['4', '5'])).
% 10.39/10.61  thf(fc1_subset_1, axiom,
% 10.39/10.61    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 10.39/10.61  thf('7', plain, (![X69 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X69))),
% 10.39/10.61      inference('cnf', [status(esa)], [fc1_subset_1])).
% 10.39/10.61  thf('8', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 10.39/10.61      inference('clc', [status(thm)], ['6', '7'])).
% 10.39/10.61  thf(d1_zfmisc_1, axiom,
% 10.39/10.61    (![A:$i,B:$i]:
% 10.39/10.61     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 10.39/10.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 10.39/10.61  thf('9', plain,
% 10.39/10.61      (![X57 : $i, X58 : $i, X59 : $i]:
% 10.39/10.61         (~ (r2_hidden @ X59 @ X58)
% 10.39/10.61          | (r1_tarski @ X59 @ X57)
% 10.39/10.61          | ((X58) != (k1_zfmisc_1 @ X57)))),
% 10.39/10.61      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 10.39/10.61  thf('10', plain,
% 10.39/10.61      (![X57 : $i, X59 : $i]:
% 10.39/10.61         ((r1_tarski @ X59 @ X57) | ~ (r2_hidden @ X59 @ (k1_zfmisc_1 @ X57)))),
% 10.39/10.61      inference('simplify', [status(thm)], ['9'])).
% 10.39/10.61  thf('11', plain, ((r1_tarski @ sk_B @ sk_A)),
% 10.39/10.61      inference('sup-', [status(thm)], ['8', '10'])).
% 10.39/10.61  thf(t28_xboole_1, axiom,
% 10.39/10.61    (![A:$i,B:$i]:
% 10.39/10.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 10.39/10.61  thf('12', plain,
% 10.39/10.61      (![X13 : $i, X14 : $i]:
% 10.39/10.61         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 10.39/10.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 10.39/10.61  thf('13', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 10.39/10.61      inference('sup-', [status(thm)], ['11', '12'])).
% 10.39/10.61  thf(t49_xboole_1, axiom,
% 10.39/10.61    (![A:$i,B:$i,C:$i]:
% 10.39/10.61     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 10.39/10.61       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 10.39/10.61  thf('14', plain,
% 10.39/10.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 10.39/10.61         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 10.39/10.61           = (k4_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X22))),
% 10.39/10.61      inference('cnf', [status(esa)], [t49_xboole_1])).
% 10.39/10.61  thf('15', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 10.39/10.61           = (k4_xboole_0 @ sk_B @ X0))),
% 10.39/10.61      inference('sup+', [status(thm)], ['13', '14'])).
% 10.39/10.61  thf('16', plain,
% 10.39/10.61      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61         = (k4_xboole_0 @ sk_B @ sk_B))),
% 10.39/10.61      inference('sup+', [status(thm)], ['3', '15'])).
% 10.39/10.61  thf(t2_boole, axiom,
% 10.39/10.61    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 10.39/10.61  thf('17', plain,
% 10.39/10.61      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 10.39/10.61      inference('cnf', [status(esa)], [t2_boole])).
% 10.39/10.61  thf(t100_xboole_1, axiom,
% 10.39/10.61    (![A:$i,B:$i]:
% 10.39/10.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 10.39/10.61  thf('18', plain,
% 10.39/10.61      (![X5 : $i, X6 : $i]:
% 10.39/10.61         ((k4_xboole_0 @ X5 @ X6)
% 10.39/10.61           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 10.39/10.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 10.39/10.61  thf('19', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 10.39/10.61      inference('sup+', [status(thm)], ['17', '18'])).
% 10.39/10.61  thf(t5_boole, axiom,
% 10.39/10.61    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 10.39/10.61  thf('20', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 10.39/10.61      inference('cnf', [status(esa)], [t5_boole])).
% 10.39/10.61  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 10.39/10.61      inference('sup+', [status(thm)], ['19', '20'])).
% 10.39/10.61  thf(t48_xboole_1, axiom,
% 10.39/10.61    (![A:$i,B:$i]:
% 10.39/10.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 10.39/10.61  thf('22', plain,
% 10.39/10.61      (![X18 : $i, X19 : $i]:
% 10.39/10.61         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 10.39/10.61           = (k3_xboole_0 @ X18 @ X19))),
% 10.39/10.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 10.39/10.61  thf('23', plain,
% 10.39/10.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 10.39/10.61      inference('sup+', [status(thm)], ['21', '22'])).
% 10.39/10.61  thf('24', plain,
% 10.39/10.61      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 10.39/10.61      inference('cnf', [status(esa)], [t2_boole])).
% 10.39/10.61  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 10.39/10.61      inference('demod', [status(thm)], ['23', '24'])).
% 10.39/10.61  thf('26', plain,
% 10.39/10.61      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 10.39/10.61      inference('demod', [status(thm)], ['16', '25'])).
% 10.39/10.61  thf(t16_xboole_1, axiom,
% 10.39/10.61    (![A:$i,B:$i,C:$i]:
% 10.39/10.61     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 10.39/10.61       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 10.39/10.61  thf('27', plain,
% 10.39/10.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 10.39/10.61         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 10.39/10.61           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 10.39/10.61      inference('cnf', [status(esa)], [t16_xboole_1])).
% 10.39/10.61  thf('28', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 10.39/10.61           = (k3_xboole_0 @ sk_B @ 
% 10.39/10.61              (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)))),
% 10.39/10.61      inference('sup+', [status(thm)], ['26', '27'])).
% 10.39/10.61  thf('29', plain,
% 10.39/10.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 10.39/10.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 10.39/10.61  thf('30', plain,
% 10.39/10.61      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 10.39/10.61      inference('cnf', [status(esa)], [t2_boole])).
% 10.39/10.61  thf('31', plain,
% 10.39/10.61      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 10.39/10.61      inference('sup+', [status(thm)], ['29', '30'])).
% 10.39/10.61  thf('32', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         ((k1_xboole_0)
% 10.39/10.61           = (k3_xboole_0 @ sk_B @ 
% 10.39/10.61              (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)))),
% 10.39/10.61      inference('demod', [status(thm)], ['28', '31'])).
% 10.39/10.61  thf('33', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         ((k1_xboole_0)
% 10.39/10.61           = (k3_xboole_0 @ sk_B @ 
% 10.39/10.61              (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))),
% 10.39/10.61      inference('sup+', [status(thm)], ['0', '32'])).
% 10.39/10.61  thf(idempotence_k3_xboole_0, axiom,
% 10.39/10.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 10.39/10.61  thf('34', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 10.39/10.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 10.39/10.61  thf(t112_xboole_1, axiom,
% 10.39/10.61    (![A:$i,B:$i,C:$i]:
% 10.39/10.61     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 10.39/10.61       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 10.39/10.61  thf('35', plain,
% 10.39/10.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 10.39/10.61         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 10.39/10.61           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 10.39/10.61      inference('cnf', [status(esa)], [t112_xboole_1])).
% 10.39/10.61  thf('36', plain,
% 10.39/10.61      (![X0 : $i, X1 : $i]:
% 10.39/10.61         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 10.39/10.61           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0))),
% 10.39/10.61      inference('sup+', [status(thm)], ['34', '35'])).
% 10.39/10.61  thf('37', plain,
% 10.39/10.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 10.39/10.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 10.39/10.61  thf('38', plain,
% 10.39/10.61      (![X0 : $i, X1 : $i]:
% 10.39/10.61         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 10.39/10.61           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 10.39/10.61      inference('demod', [status(thm)], ['36', '37'])).
% 10.39/10.61  thf('39', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 10.39/10.61           k1_xboole_0)
% 10.39/10.61           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 10.39/10.61              (k5_xboole_0 @ 
% 10.39/10.61               (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ sk_B)))),
% 10.39/10.61      inference('sup+', [status(thm)], ['33', '38'])).
% 10.39/10.61  thf(commutativity_k5_xboole_0, axiom,
% 10.39/10.61    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 10.39/10.61  thf('40', plain,
% 10.39/10.61      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 10.39/10.61      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 10.39/10.61  thf('41', plain,
% 10.39/10.61      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 10.39/10.61      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 10.39/10.61  thf('42', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 10.39/10.61      inference('cnf', [status(esa)], [t5_boole])).
% 10.39/10.61  thf('43', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.39/10.61      inference('sup+', [status(thm)], ['41', '42'])).
% 10.39/10.61  thf('44', plain,
% 10.39/10.61      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 10.39/10.61      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 10.39/10.61  thf('45', plain,
% 10.39/10.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 10.39/10.61         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 10.39/10.61           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 10.39/10.61      inference('cnf', [status(esa)], [t16_xboole_1])).
% 10.39/10.61  thf('46', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         ((k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61           = (k3_xboole_0 @ X0 @ 
% 10.39/10.61              (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 10.39/10.61               (k5_xboole_0 @ sk_B @ 
% 10.39/10.61                (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))))),
% 10.39/10.61      inference('demod', [status(thm)], ['39', '40', '43', '44', '45'])).
% 10.39/10.61  thf('47', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         ((k1_xboole_0)
% 10.39/10.61           = (k3_xboole_0 @ sk_B @ 
% 10.39/10.61              (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))),
% 10.39/10.61      inference('sup+', [status(thm)], ['0', '32'])).
% 10.39/10.61  thf(t94_xboole_1, axiom,
% 10.39/10.61    (![A:$i,B:$i]:
% 10.39/10.61     ( ( k2_xboole_0 @ A @ B ) =
% 10.39/10.61       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 10.39/10.61  thf('48', plain,
% 10.39/10.61      (![X27 : $i, X28 : $i]:
% 10.39/10.61         ((k2_xboole_0 @ X27 @ X28)
% 10.39/10.61           = (k5_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ 
% 10.39/10.61              (k3_xboole_0 @ X27 @ X28)))),
% 10.39/10.61      inference('cnf', [status(esa)], [t94_xboole_1])).
% 10.39/10.61  thf(l51_zfmisc_1, axiom,
% 10.39/10.61    (![A:$i,B:$i]:
% 10.39/10.61     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 10.39/10.61  thf('49', plain,
% 10.39/10.61      (![X61 : $i, X62 : $i]:
% 10.39/10.61         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 10.39/10.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 10.39/10.61  thf(t91_xboole_1, axiom,
% 10.39/10.61    (![A:$i,B:$i,C:$i]:
% 10.39/10.61     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 10.39/10.61       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 10.39/10.61  thf('50', plain,
% 10.39/10.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 10.39/10.61         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 10.39/10.61           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 10.39/10.61      inference('cnf', [status(esa)], [t91_xboole_1])).
% 10.39/10.61  thf('51', plain,
% 10.39/10.61      (![X27 : $i, X28 : $i]:
% 10.39/10.61         ((k3_tarski @ (k2_tarski @ X27 @ X28))
% 10.39/10.61           = (k5_xboole_0 @ X27 @ 
% 10.39/10.61              (k5_xboole_0 @ X28 @ (k3_xboole_0 @ X27 @ X28))))),
% 10.39/10.61      inference('demod', [status(thm)], ['48', '49', '50'])).
% 10.39/10.61  thf('52', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         ((k3_tarski @ 
% 10.39/10.61           (k2_tarski @ sk_B @ (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))
% 10.39/10.61           = (k5_xboole_0 @ sk_B @ 
% 10.39/10.61              (k5_xboole_0 @ 
% 10.39/10.61               (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ k1_xboole_0)))),
% 10.39/10.61      inference('sup+', [status(thm)], ['47', '51'])).
% 10.39/10.61  thf('53', plain,
% 10.39/10.61      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 10.39/10.61      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 10.39/10.61  thf('54', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.39/10.61      inference('sup+', [status(thm)], ['41', '42'])).
% 10.39/10.61  thf('55', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         ((k3_tarski @ 
% 10.39/10.61           (k2_tarski @ sk_B @ (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))
% 10.39/10.61           = (k5_xboole_0 @ sk_B @ 
% 10.39/10.61              (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))),
% 10.39/10.61      inference('demod', [status(thm)], ['52', '53', '54'])).
% 10.39/10.61  thf('56', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         ((k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61           = (k3_xboole_0 @ X0 @ 
% 10.39/10.61              (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 10.39/10.61               (k3_tarski @ 
% 10.39/10.61                (k2_tarski @ sk_B @ 
% 10.39/10.61                 (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)))))))),
% 10.39/10.61      inference('demod', [status(thm)], ['46', '55'])).
% 10.39/10.61  thf('57', plain,
% 10.39/10.61      (![X18 : $i, X19 : $i]:
% 10.39/10.61         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 10.39/10.61           = (k3_xboole_0 @ X18 @ X19))),
% 10.39/10.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 10.39/10.61  thf(t36_xboole_1, axiom,
% 10.39/10.61    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 10.39/10.61  thf('58', plain,
% 10.39/10.61      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 10.39/10.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 10.39/10.61  thf('59', plain,
% 10.39/10.61      (![X56 : $i, X57 : $i, X58 : $i]:
% 10.39/10.61         (~ (r1_tarski @ X56 @ X57)
% 10.39/10.61          | (r2_hidden @ X56 @ X58)
% 10.39/10.61          | ((X58) != (k1_zfmisc_1 @ X57)))),
% 10.39/10.61      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 10.39/10.61  thf('60', plain,
% 10.39/10.61      (![X56 : $i, X57 : $i]:
% 10.39/10.61         ((r2_hidden @ X56 @ (k1_zfmisc_1 @ X57)) | ~ (r1_tarski @ X56 @ X57))),
% 10.39/10.61      inference('simplify', [status(thm)], ['59'])).
% 10.39/10.61  thf('61', plain,
% 10.39/10.61      (![X0 : $i, X1 : $i]:
% 10.39/10.61         (r2_hidden @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 10.39/10.61      inference('sup-', [status(thm)], ['58', '60'])).
% 10.39/10.61  thf('62', plain,
% 10.39/10.61      (![X63 : $i, X64 : $i]:
% 10.39/10.61         (~ (r2_hidden @ X63 @ X64)
% 10.39/10.61          | (m1_subset_1 @ X63 @ X64)
% 10.39/10.61          | (v1_xboole_0 @ X64))),
% 10.39/10.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 10.39/10.61  thf('63', plain,
% 10.39/10.61      (![X0 : $i, X1 : $i]:
% 10.39/10.61         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 10.39/10.61          | (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 10.39/10.61      inference('sup-', [status(thm)], ['61', '62'])).
% 10.39/10.61  thf('64', plain, (![X69 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X69))),
% 10.39/10.61      inference('cnf', [status(esa)], [fc1_subset_1])).
% 10.39/10.61  thf('65', plain,
% 10.39/10.61      (![X0 : $i, X1 : $i]:
% 10.39/10.61         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 10.39/10.61      inference('clc', [status(thm)], ['63', '64'])).
% 10.39/10.61  thf('66', plain,
% 10.39/10.61      (![X0 : $i, X1 : $i]:
% 10.39/10.61         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 10.39/10.61      inference('sup+', [status(thm)], ['57', '65'])).
% 10.39/10.61  thf('67', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 10.39/10.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.39/10.61  thf(redefinition_k4_subset_1, axiom,
% 10.39/10.61    (![A:$i,B:$i,C:$i]:
% 10.39/10.61     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 10.39/10.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 10.39/10.61       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 10.39/10.61  thf('68', plain,
% 10.39/10.61      (![X70 : $i, X71 : $i, X72 : $i]:
% 10.39/10.61         (~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ X71))
% 10.39/10.61          | ~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ X71))
% 10.39/10.61          | ((k4_subset_1 @ X71 @ X70 @ X72) = (k2_xboole_0 @ X70 @ X72)))),
% 10.39/10.61      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 10.39/10.61  thf('69', plain,
% 10.39/10.61      (![X61 : $i, X62 : $i]:
% 10.39/10.61         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 10.39/10.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 10.39/10.61  thf('70', plain,
% 10.39/10.61      (![X70 : $i, X71 : $i, X72 : $i]:
% 10.39/10.61         (~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ X71))
% 10.39/10.61          | ~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ X71))
% 10.39/10.61          | ((k4_subset_1 @ X71 @ X70 @ X72)
% 10.39/10.61              = (k3_tarski @ (k2_tarski @ X70 @ X72))))),
% 10.39/10.61      inference('demod', [status(thm)], ['68', '69'])).
% 10.39/10.61  thf('71', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 10.39/10.61            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 10.39/10.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 10.39/10.61      inference('sup-', [status(thm)], ['67', '70'])).
% 10.39/10.61  thf('72', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         ((k4_subset_1 @ sk_A @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 10.39/10.61           = (k3_tarski @ (k2_tarski @ sk_B @ (k3_xboole_0 @ sk_A @ X0))))),
% 10.39/10.61      inference('sup-', [status(thm)], ['66', '71'])).
% 10.39/10.61  thf('73', plain,
% 10.39/10.61      (((k4_subset_1 @ sk_A @ sk_B @ 
% 10.39/10.61         (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))
% 10.39/10.61         = (k3_tarski @ 
% 10.39/10.61            (k2_tarski @ sk_B @ 
% 10.39/10.61             (k3_xboole_0 @ sk_A @ 
% 10.39/10.61              (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 10.39/10.61               (k3_tarski @ 
% 10.39/10.61                (k2_tarski @ sk_B @ 
% 10.39/10.61                 (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))))))))),
% 10.39/10.61      inference('sup+', [status(thm)], ['56', '72'])).
% 10.39/10.61  thf('74', plain,
% 10.39/10.61      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 10.39/10.61      inference('sup-', [status(thm)], ['1', '2'])).
% 10.39/10.61  thf('75', plain,
% 10.39/10.61      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 10.39/10.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 10.39/10.61  thf('76', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 10.39/10.61      inference('sup+', [status(thm)], ['74', '75'])).
% 10.39/10.61  thf('77', plain,
% 10.39/10.61      (![X13 : $i, X14 : $i]:
% 10.39/10.61         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 10.39/10.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 10.39/10.61  thf('78', plain,
% 10.39/10.61      (((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)
% 10.39/10.61         = (k3_subset_1 @ sk_A @ sk_B))),
% 10.39/10.61      inference('sup-', [status(thm)], ['76', '77'])).
% 10.39/10.61  thf('79', plain,
% 10.39/10.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 10.39/10.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 10.39/10.61  thf('80', plain,
% 10.39/10.61      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61         = (k3_subset_1 @ sk_A @ sk_B))),
% 10.39/10.61      inference('demod', [status(thm)], ['78', '79'])).
% 10.39/10.61  thf('81', plain,
% 10.39/10.61      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61         = (k3_subset_1 @ sk_A @ sk_B))),
% 10.39/10.61      inference('demod', [status(thm)], ['78', '79'])).
% 10.39/10.61  thf('82', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 10.39/10.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 10.39/10.61  thf('83', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 10.39/10.61      inference('sup-', [status(thm)], ['11', '12'])).
% 10.39/10.61  thf('84', plain,
% 10.39/10.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 10.39/10.61         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 10.39/10.61           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 10.39/10.61      inference('cnf', [status(esa)], [t16_xboole_1])).
% 10.39/10.61  thf('85', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         ((k3_xboole_0 @ sk_B @ X0)
% 10.39/10.61           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 10.39/10.61      inference('sup+', [status(thm)], ['83', '84'])).
% 10.39/10.61  thf('86', plain,
% 10.39/10.61      (![X27 : $i, X28 : $i]:
% 10.39/10.61         ((k3_tarski @ (k2_tarski @ X27 @ X28))
% 10.39/10.61           = (k5_xboole_0 @ X27 @ 
% 10.39/10.61              (k5_xboole_0 @ X28 @ (k3_xboole_0 @ X27 @ X28))))),
% 10.39/10.61      inference('demod', [status(thm)], ['48', '49', '50'])).
% 10.39/10.61  thf('87', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         ((k3_tarski @ (k2_tarski @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))
% 10.39/10.61           = (k5_xboole_0 @ sk_B @ 
% 10.39/10.61              (k5_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 10.39/10.61               (k3_xboole_0 @ sk_B @ X0))))),
% 10.39/10.61      inference('sup+', [status(thm)], ['85', '86'])).
% 10.39/10.61  thf('88', plain,
% 10.39/10.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 10.39/10.61         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 10.39/10.61           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 10.39/10.61      inference('cnf', [status(esa)], [t112_xboole_1])).
% 10.39/10.61  thf('89', plain,
% 10.39/10.61      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 10.39/10.61      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 10.39/10.61  thf('90', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         ((k3_tarski @ (k2_tarski @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))
% 10.39/10.61           = (k5_xboole_0 @ sk_B @ 
% 10.39/10.61              (k3_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_A) @ X0)))),
% 10.39/10.61      inference('demod', [status(thm)], ['87', '88', '89'])).
% 10.39/10.61  thf('91', plain,
% 10.39/10.61      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61         = (k3_subset_1 @ sk_A @ sk_B))),
% 10.39/10.61      inference('demod', [status(thm)], ['78', '79'])).
% 10.39/10.61  thf('92', plain,
% 10.39/10.61      (![X5 : $i, X6 : $i]:
% 10.39/10.61         ((k4_xboole_0 @ X5 @ X6)
% 10.39/10.61           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 10.39/10.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 10.39/10.61  thf('93', plain,
% 10.39/10.61      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61         = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 10.39/10.61      inference('sup+', [status(thm)], ['91', '92'])).
% 10.39/10.61  thf('94', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 10.39/10.61      inference('sup+', [status(thm)], ['74', '75'])).
% 10.39/10.61  thf('95', plain,
% 10.39/10.61      (![X56 : $i, X57 : $i]:
% 10.39/10.61         ((r2_hidden @ X56 @ (k1_zfmisc_1 @ X57)) | ~ (r1_tarski @ X56 @ X57))),
% 10.39/10.61      inference('simplify', [status(thm)], ['59'])).
% 10.39/10.61  thf('96', plain,
% 10.39/10.61      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 10.39/10.61      inference('sup-', [status(thm)], ['94', '95'])).
% 10.39/10.61  thf('97', plain,
% 10.39/10.61      (![X63 : $i, X64 : $i]:
% 10.39/10.61         (~ (r2_hidden @ X63 @ X64)
% 10.39/10.61          | (m1_subset_1 @ X63 @ X64)
% 10.39/10.61          | (v1_xboole_0 @ X64))),
% 10.39/10.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 10.39/10.61  thf('98', plain,
% 10.39/10.61      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 10.39/10.61        | (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 10.39/10.61      inference('sup-', [status(thm)], ['96', '97'])).
% 10.39/10.61  thf('99', plain, (![X69 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X69))),
% 10.39/10.61      inference('cnf', [status(esa)], [fc1_subset_1])).
% 10.39/10.61  thf('100', plain,
% 10.39/10.61      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 10.39/10.61      inference('clc', [status(thm)], ['98', '99'])).
% 10.39/10.61  thf('101', plain,
% 10.39/10.61      (![X67 : $i, X68 : $i]:
% 10.39/10.61         (((k3_subset_1 @ X67 @ X68) = (k4_xboole_0 @ X67 @ X68))
% 10.39/10.61          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ X67)))),
% 10.39/10.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 10.39/10.61  thf('102', plain,
% 10.39/10.61      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 10.39/10.61      inference('sup-', [status(thm)], ['100', '101'])).
% 10.39/10.61  thf('103', plain,
% 10.39/10.61      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61         = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 10.39/10.61      inference('demod', [status(thm)], ['93', '102'])).
% 10.39/10.61  thf('104', plain,
% 10.39/10.61      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 10.39/10.61      inference('sup-', [status(thm)], ['1', '2'])).
% 10.39/10.61  thf('105', plain,
% 10.39/10.61      (![X18 : $i, X19 : $i]:
% 10.39/10.61         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 10.39/10.61           = (k3_xboole_0 @ X18 @ X19))),
% 10.39/10.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 10.39/10.61  thf('106', plain,
% 10.39/10.61      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61         = (k3_xboole_0 @ sk_A @ sk_B))),
% 10.39/10.61      inference('sup+', [status(thm)], ['104', '105'])).
% 10.39/10.61  thf('107', plain,
% 10.39/10.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 10.39/10.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 10.39/10.61  thf('108', plain,
% 10.39/10.61      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61         = (k3_xboole_0 @ sk_B @ sk_A))),
% 10.39/10.61      inference('demod', [status(thm)], ['106', '107'])).
% 10.39/10.61  thf('109', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 10.39/10.61      inference('sup-', [status(thm)], ['11', '12'])).
% 10.39/10.61  thf('110', plain,
% 10.39/10.61      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 10.39/10.61      inference('demod', [status(thm)], ['108', '109'])).
% 10.39/10.61  thf('111', plain,
% 10.39/10.61      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 10.39/10.61      inference('sup-', [status(thm)], ['100', '101'])).
% 10.39/10.61  thf('112', plain,
% 10.39/10.61      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 10.39/10.61      inference('sup+', [status(thm)], ['110', '111'])).
% 10.39/10.61  thf('113', plain,
% 10.39/10.61      (((sk_B) = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 10.39/10.61      inference('demod', [status(thm)], ['103', '112'])).
% 10.39/10.61  thf('114', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 10.39/10.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 10.39/10.61  thf('115', plain,
% 10.39/10.61      (![X5 : $i, X6 : $i]:
% 10.39/10.61         ((k4_xboole_0 @ X5 @ X6)
% 10.39/10.61           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 10.39/10.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 10.39/10.61  thf('116', plain,
% 10.39/10.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 10.39/10.61      inference('sup+', [status(thm)], ['114', '115'])).
% 10.39/10.61  thf('117', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 10.39/10.61      inference('demod', [status(thm)], ['23', '24'])).
% 10.39/10.61  thf('118', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 10.39/10.61      inference('demod', [status(thm)], ['116', '117'])).
% 10.39/10.61  thf('119', plain,
% 10.39/10.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 10.39/10.61         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 10.39/10.61           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 10.39/10.61      inference('cnf', [status(esa)], [t91_xboole_1])).
% 10.39/10.61  thf('120', plain,
% 10.39/10.61      (![X0 : $i, X1 : $i]:
% 10.39/10.61         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 10.39/10.61           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 10.39/10.61      inference('sup+', [status(thm)], ['118', '119'])).
% 10.39/10.61  thf('121', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.39/10.61      inference('sup+', [status(thm)], ['41', '42'])).
% 10.39/10.61  thf('122', plain,
% 10.39/10.61      (![X0 : $i, X1 : $i]:
% 10.39/10.61         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 10.39/10.61      inference('demod', [status(thm)], ['120', '121'])).
% 10.39/10.61  thf('123', plain,
% 10.39/10.61      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 10.39/10.61      inference('sup+', [status(thm)], ['113', '122'])).
% 10.39/10.61  thf('124', plain,
% 10.39/10.61      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 10.39/10.61      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 10.39/10.61  thf('125', plain,
% 10.39/10.61      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 10.39/10.61      inference('demod', [status(thm)], ['123', '124'])).
% 10.39/10.61  thf('126', plain,
% 10.39/10.61      (![X0 : $i]:
% 10.39/10.61         ((k3_tarski @ (k2_tarski @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))
% 10.39/10.61           = (k5_xboole_0 @ sk_B @ 
% 10.39/10.61              (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)))),
% 10.39/10.61      inference('demod', [status(thm)], ['90', '125'])).
% 10.39/10.61  thf('127', plain,
% 10.39/10.61      (((k3_tarski @ 
% 10.39/10.61         (k2_tarski @ sk_B @ (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))))
% 10.39/10.61         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 10.39/10.61      inference('sup+', [status(thm)], ['82', '126'])).
% 10.39/10.61  thf('128', plain,
% 10.39/10.61      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61         = (k3_subset_1 @ sk_A @ sk_B))),
% 10.39/10.61      inference('demod', [status(thm)], ['78', '79'])).
% 10.39/10.61  thf('129', plain,
% 10.39/10.61      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 10.39/10.61      inference('demod', [status(thm)], ['123', '124'])).
% 10.39/10.61  thf('130', plain,
% 10.39/10.61      (![X0 : $i, X1 : $i]:
% 10.39/10.61         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 10.39/10.61      inference('demod', [status(thm)], ['120', '121'])).
% 10.39/10.61  thf('131', plain,
% 10.39/10.61      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 10.39/10.61      inference('sup+', [status(thm)], ['129', '130'])).
% 10.39/10.61  thf('132', plain,
% 10.39/10.61      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) = (sk_A))),
% 10.39/10.61      inference('demod', [status(thm)], ['127', '128', '131'])).
% 10.39/10.61  thf('133', plain,
% 10.39/10.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 10.39/10.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 10.39/10.61  thf('134', plain,
% 10.39/10.61      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61         = (k3_subset_1 @ sk_A @ sk_B))),
% 10.39/10.61      inference('demod', [status(thm)], ['78', '79'])).
% 10.39/10.61  thf('135', plain,
% 10.39/10.61      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61         = (k3_subset_1 @ sk_A @ sk_B))),
% 10.39/10.61      inference('demod', [status(thm)], ['78', '79'])).
% 10.39/10.61  thf('136', plain,
% 10.39/10.61      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61         = (k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 10.39/10.61      inference('demod', [status(thm)],
% 10.39/10.61                ['73', '80', '81', '132', '133', '134', '135'])).
% 10.39/10.61  thf('137', plain,
% 10.39/10.61      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) = (sk_A))),
% 10.39/10.61      inference('demod', [status(thm)], ['127', '128', '131'])).
% 10.39/10.61  thf('138', plain,
% 10.39/10.61      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 10.39/10.61      inference('demod', [status(thm)], ['136', '137'])).
% 10.39/10.61  thf('139', plain,
% 10.39/10.61      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 10.39/10.61         != (k2_subset_1 @ sk_A))),
% 10.39/10.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.39/10.61  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 10.39/10.61  thf('140', plain, (![X66 : $i]: ((k2_subset_1 @ X66) = (X66))),
% 10.39/10.61      inference('cnf', [status(esa)], [d4_subset_1])).
% 10.39/10.61  thf('141', plain,
% 10.39/10.61      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 10.39/10.61      inference('demod', [status(thm)], ['139', '140'])).
% 10.39/10.61  thf('142', plain, ($false),
% 10.39/10.61      inference('simplify_reflect-', [status(thm)], ['138', '141'])).
% 10.39/10.61  
% 10.39/10.61  % SZS output end Refutation
% 10.39/10.61  
% 10.39/10.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
