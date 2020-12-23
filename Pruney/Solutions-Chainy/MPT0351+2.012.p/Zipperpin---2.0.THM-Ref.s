%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X9iJJXN7BW

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:58 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 187 expanded)
%              Number of leaves         :   33 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  627 (1241 expanded)
%              Number of equality atoms :   70 ( 137 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','35'])).

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

thf('37',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('38',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('39',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('40',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['37','38','39'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X26 ) @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('42',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('43',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) )
      | ( ( k4_subset_1 @ X31 @ X30 @ X32 )
        = ( k2_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('51',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ( r2_hidden @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('60',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('62',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('64',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','35'])).

thf('66',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ( k5_xboole_0 @ sk_A @ k1_xboole_0 )
 != sk_A ),
    inference(demod,[status(thm)],['48','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ X0 @ X0 ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['36','67'])).

thf('69',plain,(
    sk_A != sk_A ),
    inference('sup-',[status(thm)],['11','68'])).

thf('70',plain,(
    $false ),
    inference(simplify,[status(thm)],['69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X9iJJXN7BW
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:43:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 113 iterations in 0.045s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(d3_tarski, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (![X3 : $i, X5 : $i]:
% 0.19/0.47         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X3 : $i, X5 : $i]:
% 0.19/0.47         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.47  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.19/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.19/0.47  thf(t28_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i]:
% 0.19/0.47         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.19/0.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.47  thf('5', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.47  thf(t100_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X7 : $i, X8 : $i]:
% 0.19/0.47         ((k4_xboole_0 @ X7 @ X8)
% 0.19/0.47           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.47  thf(t98_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X17 : $i, X18 : $i]:
% 0.19/0.47         ((k2_xboole_0 @ X17 @ X18)
% 0.19/0.47           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((k2_xboole_0 @ X0 @ X0)
% 0.19/0.47           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.19/0.47      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.47  thf(idempotence_k2_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.47  thf('10', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.19/0.47      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.19/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.47  thf(t3_boole, axiom,
% 0.19/0.47    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.47  thf('12', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.19/0.47      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.47  thf(t48_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X13 : $i, X14 : $i]:
% 0.19/0.47         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.19/0.47           = (k3_xboole_0 @ X13 @ X14))),
% 0.19/0.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['12', '13'])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.19/0.47  thf('17', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.19/0.47      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      (![X17 : $i, X18 : $i]:
% 0.19/0.47         ((k2_xboole_0 @ X17 @ X18)
% 0.19/0.47           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['17', '18'])).
% 0.19/0.47  thf(commutativity_k2_tarski, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      (![X19 : $i, X20 : $i]:
% 0.19/0.47         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 0.19/0.47      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.19/0.47  thf(l51_zfmisc_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      (![X23 : $i, X24 : $i]:
% 0.19/0.47         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 0.19/0.47      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('sup+', [status(thm)], ['20', '21'])).
% 0.19/0.47  thf('23', plain,
% 0.19/0.47      (![X23 : $i, X24 : $i]:
% 0.19/0.47         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 0.19/0.47      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.47  thf('24', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('sup+', [status(thm)], ['22', '23'])).
% 0.19/0.47  thf(t1_boole, axiom,
% 0.19/0.47    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.47  thf('25', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.19/0.47      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.47  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['24', '25'])).
% 0.19/0.47  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['19', '26'])).
% 0.19/0.47  thf('28', plain,
% 0.19/0.47      (![X7 : $i, X8 : $i]:
% 0.19/0.47         ((k4_xboole_0 @ X7 @ X8)
% 0.19/0.47           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.47  thf('29', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['27', '28'])).
% 0.19/0.47  thf(t51_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.19/0.47       ( A ) ))).
% 0.19/0.47  thf('30', plain,
% 0.19/0.47      (![X15 : $i, X16 : $i]:
% 0.19/0.47         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 0.19/0.47           = (X15))),
% 0.19/0.47      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.19/0.47  thf('31', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((k2_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.19/0.47           (k3_xboole_0 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['29', '30'])).
% 0.19/0.47  thf('32', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.19/0.47      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.19/0.47  thf('33', plain,
% 0.19/0.47      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.47  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.47  thf('34', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.47  thf('35', plain,
% 0.19/0.47      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['33', '34'])).
% 0.19/0.47  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['16', '35'])).
% 0.19/0.47  thf(t28_subset_1, conjecture,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.47       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i]:
% 0.19/0.47        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.47          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.19/0.47  thf('37', plain,
% 0.19/0.47      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.19/0.47         != (k2_subset_1 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.47  thf('38', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 0.19/0.47      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.47  thf('39', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 0.19/0.47      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.47  thf('40', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.19/0.47  thf(dt_k2_subset_1, axiom,
% 0.19/0.47    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.47  thf('41', plain,
% 0.19/0.47      (![X26 : $i]: (m1_subset_1 @ (k2_subset_1 @ X26) @ (k1_zfmisc_1 @ X26))),
% 0.19/0.47      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.19/0.47  thf('42', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 0.19/0.47      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.47  thf('43', plain, (![X26 : $i]: (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X26))),
% 0.19/0.47      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.47  thf('44', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(redefinition_k4_subset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.19/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.47       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.19/0.47  thf('45', plain,
% 0.19/0.47      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 0.19/0.47          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31))
% 0.19/0.47          | ((k4_subset_1 @ X31 @ X30 @ X32) = (k2_xboole_0 @ X30 @ X32)))),
% 0.19/0.47      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.19/0.47  thf('46', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.19/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.47  thf('47', plain,
% 0.19/0.47      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['43', '46'])).
% 0.19/0.47  thf('48', plain, (((k2_xboole_0 @ sk_B @ sk_A) != (sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['40', '47'])).
% 0.19/0.47  thf('49', plain,
% 0.19/0.47      (![X3 : $i, X5 : $i]:
% 0.19/0.47         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.47  thf('50', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(l3_subset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.19/0.47  thf('51', plain,
% 0.19/0.47      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X27 @ X28)
% 0.19/0.47          | (r2_hidden @ X27 @ X29)
% 0.19/0.47          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 0.19/0.47      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.19/0.47  thf('52', plain,
% 0.19/0.47      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.19/0.47      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.47  thf('53', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['49', '52'])).
% 0.19/0.47  thf('54', plain,
% 0.19/0.47      (![X3 : $i, X5 : $i]:
% 0.19/0.47         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.47  thf('55', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.47  thf('56', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.47      inference('simplify', [status(thm)], ['55'])).
% 0.19/0.47  thf('57', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i]:
% 0.19/0.47         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.19/0.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.47  thf('58', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.19/0.47      inference('sup-', [status(thm)], ['56', '57'])).
% 0.19/0.47  thf('59', plain,
% 0.19/0.47      (![X7 : $i, X8 : $i]:
% 0.19/0.47         ((k4_xboole_0 @ X7 @ X8)
% 0.19/0.47           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.47  thf('60', plain,
% 0.19/0.47      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.19/0.47      inference('sup+', [status(thm)], ['58', '59'])).
% 0.19/0.47  thf('61', plain,
% 0.19/0.47      (![X17 : $i, X18 : $i]:
% 0.19/0.47         ((k2_xboole_0 @ X17 @ X18)
% 0.19/0.47           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.19/0.47  thf('62', plain,
% 0.19/0.47      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.19/0.47         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 0.19/0.47      inference('sup+', [status(thm)], ['60', '61'])).
% 0.19/0.47  thf('63', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('sup+', [status(thm)], ['22', '23'])).
% 0.19/0.47  thf('64', plain,
% 0.19/0.47      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.19/0.47         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 0.19/0.47      inference('demod', [status(thm)], ['62', '63'])).
% 0.19/0.47  thf('65', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['16', '35'])).
% 0.19/0.47  thf('66', plain,
% 0.19/0.47      (((k2_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['64', '65'])).
% 0.19/0.47  thf('67', plain, (((k5_xboole_0 @ sk_A @ k1_xboole_0) != (sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['48', '66'])).
% 0.19/0.47  thf('68', plain,
% 0.19/0.47      (![X0 : $i]: ((k5_xboole_0 @ sk_A @ (k5_xboole_0 @ X0 @ X0)) != (sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['36', '67'])).
% 0.19/0.47  thf('69', plain, (((sk_A) != (sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['11', '68'])).
% 0.19/0.47  thf('70', plain, ($false), inference('simplify', [status(thm)], ['69'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
