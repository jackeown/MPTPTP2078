%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nDEyWrgnwk

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:01 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 160 expanded)
%              Number of leaves         :   36 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  655 ( 988 expanded)
%              Number of equality atoms :   66 ( 106 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ( r2_hidden @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ X0 )
      = ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X26: $i] :
      ( ( k1_subset_1 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X30 ) @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('24',plain,(
    ! [X27: $i] :
      ( ( k2_subset_1 @ X27 )
      = X27 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('25',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('29',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X32 @ ( k3_subset_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X26: $i] :
      ( ( k1_subset_1 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X39: $i] :
      ( ( k2_subset_1 @ X39 )
      = ( k3_subset_1 @ X39 @ ( k1_subset_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('33',plain,(
    ! [X27: $i] :
      ( ( k2_subset_1 @ X27 )
      = X27 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('34',plain,(
    ! [X39: $i] :
      ( X39
      = ( k3_subset_1 @ X39 @ ( k1_subset_1 @ X39 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('39',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('42',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X1 @ ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','45'])).

thf('47',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['21','46'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('49',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','36'])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('53',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['49','54'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('56',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_tarski @ X18 @ X17 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('57',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['55','60'])).

thf('62',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X27: $i] :
      ( ( k2_subset_1 @ X27 )
      = X27 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('64',plain,(
    ! [X27: $i] :
      ( ( k2_subset_1 @ X27 )
      = X27 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('65',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k4_subset_1 @ X37 @ X36 @ X38 )
        = ( k2_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['65','70'])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nDEyWrgnwk
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 280 iterations in 0.130s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.58  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.38/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.58  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.38/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.58  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(d3_tarski, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      (![X1 : $i, X3 : $i]:
% 0.38/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (![X1 : $i, X3 : $i]:
% 0.38/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.58  thf(t28_subset_1, conjecture,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.58       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i,B:$i]:
% 0.38/0.58        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.58          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.38/0.58  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(l3_subset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X33 @ X34)
% 0.38/0.58          | (r2_hidden @ X33 @ X35)
% 0.38/0.58          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.38/0.58      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['1', '4'])).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (![X1 : $i, X3 : $i]:
% 0.38/0.58         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.58  thf('7', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.58  thf('8', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.38/0.58      inference('simplify', [status(thm)], ['7'])).
% 0.38/0.58  thf(t28_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i]:
% 0.38/0.58         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.58  thf('10', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.58  thf(t48_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X13 : $i, X14 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.38/0.58           = (k3_xboole_0 @ X13 @ X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.58  thf(d5_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.38/0.58       ( ![D:$i]:
% 0.38/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.58           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X8 @ X7)
% 0.38/0.58          | ~ (r2_hidden @ X8 @ X6)
% 0.38/0.58          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X8 @ X6)
% 0.38/0.58          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['12'])).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.58          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['11', '13'])).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X0 @ sk_B)
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['10', '14'])).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X8 @ X7)
% 0.38/0.58          | (r2_hidden @ X8 @ X5)
% 0.38/0.58          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.38/0.58         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ sk_A))),
% 0.38/0.58      inference('clc', [status(thm)], ['15', '17'])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_A) @ X0)),
% 0.38/0.58      inference('sup-', [status(thm)], ['0', '18'])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i]:
% 0.38/0.58         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ X0)
% 0.38/0.58           = (k4_xboole_0 @ sk_B @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.58  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.38/0.58  thf('22', plain, (![X26 : $i]: ((k1_subset_1 @ X26) = (k1_xboole_0))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.38/0.58  thf(dt_k2_subset_1, axiom,
% 0.38/0.58    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      (![X30 : $i]: (m1_subset_1 @ (k2_subset_1 @ X30) @ (k1_zfmisc_1 @ X30))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.38/0.58  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.38/0.58  thf('24', plain, (![X27 : $i]: ((k2_subset_1 @ X27) = (X27))),
% 0.38/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.38/0.58  thf('25', plain, (![X30 : $i]: (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X30))),
% 0.38/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.38/0.58  thf(d5_subset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.58       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      (![X28 : $i, X29 : $i]:
% 0.38/0.58         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 0.38/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.58  thf(t4_subset_1, axiom,
% 0.38/0.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      (![X40 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 0.38/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.58  thf(involutiveness_k3_subset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.58       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      (![X31 : $i, X32 : $i]:
% 0.38/0.58         (((k3_subset_1 @ X32 @ (k3_subset_1 @ X32 @ X31)) = (X31))
% 0.38/0.58          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 0.38/0.58      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.38/0.58  thf('30', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.58  thf('31', plain, (![X26 : $i]: ((k1_subset_1 @ X26) = (k1_xboole_0))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.38/0.58  thf(t22_subset_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.38/0.58  thf('32', plain,
% 0.38/0.58      (![X39 : $i]:
% 0.38/0.58         ((k2_subset_1 @ X39) = (k3_subset_1 @ X39 @ (k1_subset_1 @ X39)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.38/0.58  thf('33', plain, (![X27 : $i]: ((k2_subset_1 @ X27) = (X27))),
% 0.38/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.38/0.58  thf('34', plain,
% 0.38/0.58      (![X39 : $i]: ((X39) = (k3_subset_1 @ X39 @ (k1_subset_1 @ X39)))),
% 0.38/0.58      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.58  thf('35', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['31', '34'])).
% 0.38/0.58  thf('36', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.58      inference('demod', [status(thm)], ['30', '35'])).
% 0.38/0.58  thf('37', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['27', '36'])).
% 0.38/0.58  thf('38', plain,
% 0.38/0.58      (![X40 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 0.38/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.58  thf('39', plain,
% 0.38/0.58      (![X28 : $i, X29 : $i]:
% 0.38/0.58         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 0.38/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.58  thf('41', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['31', '34'])).
% 0.38/0.58  thf('42', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.38/0.58  thf('43', plain,
% 0.38/0.58      (![X13 : $i, X14 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.38/0.58           = (k3_xboole_0 @ X13 @ X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.58  thf('44', plain,
% 0.38/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['42', '43'])).
% 0.38/0.58  thf('45', plain,
% 0.38/0.58      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['37', '44'])).
% 0.38/0.58  thf('46', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_subset_1 @ X0)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['22', '45'])).
% 0.38/0.58  thf('47', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_A))),
% 0.38/0.58      inference('sup+', [status(thm)], ['21', '46'])).
% 0.38/0.58  thf(t98_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.38/0.58  thf('48', plain,
% 0.38/0.58      (![X15 : $i, X16 : $i]:
% 0.38/0.58         ((k2_xboole_0 @ X15 @ X16)
% 0.38/0.58           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.38/0.58  thf('49', plain,
% 0.38/0.58      (((k2_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['47', '48'])).
% 0.38/0.58  thf('50', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['27', '36'])).
% 0.38/0.58  thf('51', plain,
% 0.38/0.58      (![X15 : $i, X16 : $i]:
% 0.38/0.58         ((k2_xboole_0 @ X15 @ X16)
% 0.38/0.58           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.38/0.58  thf(idempotence_k2_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.38/0.58  thf('53', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ X10) = (X10))),
% 0.38/0.58      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.38/0.58  thf('54', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.58      inference('demod', [status(thm)], ['52', '53'])).
% 0.38/0.58  thf('55', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['49', '54'])).
% 0.38/0.58  thf(commutativity_k2_tarski, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.38/0.58  thf('56', plain,
% 0.38/0.58      (![X17 : $i, X18 : $i]:
% 0.38/0.58         ((k2_tarski @ X18 @ X17) = (k2_tarski @ X17 @ X18))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.38/0.58  thf(l51_zfmisc_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.58  thf('57', plain,
% 0.38/0.58      (![X24 : $i, X25 : $i]:
% 0.38/0.58         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 0.38/0.58      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.58  thf('58', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('sup+', [status(thm)], ['56', '57'])).
% 0.38/0.58  thf('59', plain,
% 0.38/0.58      (![X24 : $i, X25 : $i]:
% 0.38/0.58         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 0.38/0.58      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.58  thf('60', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('sup+', [status(thm)], ['58', '59'])).
% 0.38/0.58  thf('61', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['55', '60'])).
% 0.38/0.59  thf('62', plain,
% 0.38/0.59      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.38/0.59         != (k2_subset_1 @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('63', plain, (![X27 : $i]: ((k2_subset_1 @ X27) = (X27))),
% 0.38/0.59      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.38/0.59  thf('64', plain, (![X27 : $i]: ((k2_subset_1 @ X27) = (X27))),
% 0.38/0.59      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.38/0.59  thf('65', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.38/0.59  thf('66', plain, (![X30 : $i]: (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X30))),
% 0.38/0.59      inference('demod', [status(thm)], ['23', '24'])).
% 0.38/0.59  thf('67', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(redefinition_k4_subset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.38/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.59       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.38/0.59  thf('68', plain,
% 0.38/0.59      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 0.38/0.59          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37))
% 0.38/0.59          | ((k4_subset_1 @ X37 @ X36 @ X38) = (k2_xboole_0 @ X36 @ X38)))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.38/0.59  thf('69', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.38/0.59  thf('70', plain,
% 0.38/0.59      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['66', '69'])).
% 0.38/0.59  thf('71', plain, (((k2_xboole_0 @ sk_B @ sk_A) != (sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['65', '70'])).
% 0.38/0.59  thf('72', plain, ($false),
% 0.38/0.59      inference('simplify_reflect-', [status(thm)], ['61', '71'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
