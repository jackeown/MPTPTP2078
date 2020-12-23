%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HetrcVG0sK

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:51 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 171 expanded)
%              Number of leaves         :   36 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  765 (1314 expanded)
%              Number of equality atoms :   72 ( 122 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k3_subset_1 @ X60 @ X61 )
        = ( k4_xboole_0 @ X60 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('4',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r1_tarski @ X49 @ X50 )
      | ( r2_hidden @ X49 @ X51 )
      | ( X51
       != ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r2_hidden @ X49 @ ( k1_zfmisc_1 @ X50 ) )
      | ~ ( r1_tarski @ X49 @ X50 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ X56 @ X57 )
      | ( m1_subset_1 @ X56 @ X57 )
      | ( v1_xboole_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ! [X56: $i,X57: $i] :
      ( ( m1_subset_1 @ X56 @ X57 )
      | ~ ( r2_hidden @ X56 @ X57 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X64 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X64 ) )
      | ( ( k4_subset_1 @ X64 @ X63 @ X65 )
        = ( k2_xboole_0 @ X63 @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X64 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X64 ) )
      | ( ( k4_subset_1 @ X64 @ X63 @ X65 )
        = ( k3_tarski @ ( k2_tarski @ X63 @ X65 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ X57 )
      | ( r2_hidden @ X56 @ X57 )
      | ( v1_xboole_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X62: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('22',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X52 @ X51 )
      | ( r1_tarski @ X52 @ X50 )
      | ( X51
       != ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('24',plain,(
    ! [X50: $i,X52: $i] :
      ( ( r1_tarski @ X52 @ X50 )
      | ~ ( r2_hidden @ X52 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['22','24'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('36',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('44',plain,
    ( sk_B_1
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['34','43'])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('46',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('47',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('48',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_tarski @ ( k2_tarski @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['44','48'])).

thf('50',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('59',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('60',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('61',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('62',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['58','62'])).

thf('64',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('67',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('69',plain,
    ( sk_A
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['49','67','68'])).

thf('70',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['17','69'])).

thf('71',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('72',plain,(
    ! [X59: $i] :
      ( ( k2_subset_1 @ X59 )
      = X59 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('73',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
 != sk_A ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HetrcVG0sK
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:40:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.51/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.73  % Solved by: fo/fo7.sh
% 0.51/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.73  % done 440 iterations in 0.232s
% 0.51/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.73  % SZS output start Refutation
% 0.51/0.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.51/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.73  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.51/0.73  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.51/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.73  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.51/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.73  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.51/0.73  thf(t25_subset_1, conjecture,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.73       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.51/0.73         ( k2_subset_1 @ A ) ) ))).
% 0.51/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.73    (~( ![A:$i,B:$i]:
% 0.51/0.73        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.73          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.51/0.73            ( k2_subset_1 @ A ) ) ) )),
% 0.51/0.73    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.51/0.73  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(d5_subset_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.73       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.51/0.73  thf('1', plain,
% 0.51/0.73      (![X60 : $i, X61 : $i]:
% 0.51/0.73         (((k3_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))
% 0.51/0.73          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X60)))),
% 0.51/0.73      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.51/0.73  thf('2', plain,
% 0.51/0.73      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.51/0.73  thf(t36_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.51/0.73  thf('3', plain,
% 0.51/0.73      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.51/0.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.51/0.73  thf('4', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.51/0.73      inference('sup+', [status(thm)], ['2', '3'])).
% 0.51/0.73  thf(d1_zfmisc_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.51/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.51/0.73  thf('5', plain,
% 0.51/0.73      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.51/0.73         (~ (r1_tarski @ X49 @ X50)
% 0.51/0.73          | (r2_hidden @ X49 @ X51)
% 0.51/0.73          | ((X51) != (k1_zfmisc_1 @ X50)))),
% 0.51/0.73      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.51/0.73  thf('6', plain,
% 0.51/0.73      (![X49 : $i, X50 : $i]:
% 0.51/0.73         ((r2_hidden @ X49 @ (k1_zfmisc_1 @ X50)) | ~ (r1_tarski @ X49 @ X50))),
% 0.51/0.73      inference('simplify', [status(thm)], ['5'])).
% 0.51/0.73  thf('7', plain,
% 0.51/0.73      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.51/0.73      inference('sup-', [status(thm)], ['4', '6'])).
% 0.51/0.73  thf(d2_subset_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( ( v1_xboole_0 @ A ) =>
% 0.51/0.73         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.51/0.73       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.51/0.73         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.51/0.73  thf('8', plain,
% 0.51/0.73      (![X56 : $i, X57 : $i]:
% 0.51/0.73         (~ (r2_hidden @ X56 @ X57)
% 0.51/0.73          | (m1_subset_1 @ X56 @ X57)
% 0.51/0.73          | (v1_xboole_0 @ X57))),
% 0.51/0.73      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.51/0.73  thf(d1_xboole_0, axiom,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.51/0.73  thf('9', plain,
% 0.51/0.73      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.51/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.73  thf('10', plain,
% 0.51/0.73      (![X56 : $i, X57 : $i]:
% 0.51/0.73         ((m1_subset_1 @ X56 @ X57) | ~ (r2_hidden @ X56 @ X57))),
% 0.51/0.73      inference('clc', [status(thm)], ['8', '9'])).
% 0.51/0.73  thf('11', plain,
% 0.51/0.73      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.51/0.73      inference('sup-', [status(thm)], ['7', '10'])).
% 0.51/0.73  thf('12', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(redefinition_k4_subset_1, axiom,
% 0.51/0.73    (![A:$i,B:$i,C:$i]:
% 0.51/0.73     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.51/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.51/0.73       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.51/0.73  thf('13', plain,
% 0.51/0.73      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X64))
% 0.51/0.73          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64))
% 0.51/0.73          | ((k4_subset_1 @ X64 @ X63 @ X65) = (k2_xboole_0 @ X63 @ X65)))),
% 0.51/0.73      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.51/0.73  thf(l51_zfmisc_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.51/0.73  thf('14', plain,
% 0.51/0.73      (![X54 : $i, X55 : $i]:
% 0.51/0.73         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.51/0.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.51/0.73  thf('15', plain,
% 0.51/0.73      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X64))
% 0.51/0.73          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64))
% 0.51/0.73          | ((k4_subset_1 @ X64 @ X63 @ X65)
% 0.51/0.73              = (k3_tarski @ (k2_tarski @ X63 @ X65))))),
% 0.51/0.73      inference('demod', [status(thm)], ['13', '14'])).
% 0.51/0.73  thf('16', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         (((k4_subset_1 @ sk_A @ sk_B_1 @ X0)
% 0.51/0.73            = (k3_tarski @ (k2_tarski @ sk_B_1 @ X0)))
% 0.51/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['12', '15'])).
% 0.51/0.73  thf('17', plain,
% 0.51/0.73      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.51/0.73         = (k3_tarski @ (k2_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['11', '16'])).
% 0.51/0.73  thf('18', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('19', plain,
% 0.51/0.73      (![X56 : $i, X57 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X56 @ X57)
% 0.51/0.73          | (r2_hidden @ X56 @ X57)
% 0.51/0.73          | (v1_xboole_0 @ X57))),
% 0.51/0.73      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.51/0.73  thf('20', plain,
% 0.51/0.73      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.51/0.73        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['18', '19'])).
% 0.51/0.73  thf(fc1_subset_1, axiom,
% 0.51/0.73    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.51/0.73  thf('21', plain, (![X62 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X62))),
% 0.51/0.73      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.51/0.73  thf('22', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.51/0.73      inference('clc', [status(thm)], ['20', '21'])).
% 0.51/0.73  thf('23', plain,
% 0.51/0.73      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.51/0.73         (~ (r2_hidden @ X52 @ X51)
% 0.51/0.73          | (r1_tarski @ X52 @ X50)
% 0.51/0.73          | ((X51) != (k1_zfmisc_1 @ X50)))),
% 0.51/0.73      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.51/0.73  thf('24', plain,
% 0.51/0.73      (![X50 : $i, X52 : $i]:
% 0.51/0.73         ((r1_tarski @ X52 @ X50) | ~ (r2_hidden @ X52 @ (k1_zfmisc_1 @ X50)))),
% 0.51/0.73      inference('simplify', [status(thm)], ['23'])).
% 0.51/0.73  thf('25', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.51/0.73      inference('sup-', [status(thm)], ['22', '24'])).
% 0.51/0.73  thf(t28_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.51/0.73  thf('26', plain,
% 0.51/0.73      (![X9 : $i, X10 : $i]:
% 0.51/0.73         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.51/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.51/0.73  thf('27', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['25', '26'])).
% 0.51/0.73  thf(commutativity_k3_xboole_0, axiom,
% 0.51/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.51/0.73  thf('28', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.73  thf(t100_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.51/0.73  thf('29', plain,
% 0.51/0.73      (![X7 : $i, X8 : $i]:
% 0.51/0.73         ((k4_xboole_0 @ X7 @ X8)
% 0.51/0.73           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.51/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.73  thf('30', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k4_xboole_0 @ X0 @ X1)
% 0.51/0.73           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['28', '29'])).
% 0.51/0.73  thf('31', plain,
% 0.51/0.73      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['27', '30'])).
% 0.51/0.73  thf('32', plain,
% 0.51/0.73      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.51/0.73  thf(commutativity_k5_xboole_0, axiom,
% 0.51/0.73    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.51/0.73  thf('33', plain,
% 0.51/0.73      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.73  thf('34', plain,
% 0.51/0.73      (((k3_subset_1 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_B_1 @ sk_A))),
% 0.51/0.73      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.51/0.73  thf('35', plain,
% 0.51/0.73      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.73  thf(t92_xboole_1, axiom,
% 0.51/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.51/0.73  thf('36', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.51/0.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.51/0.73  thf(t91_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i,C:$i]:
% 0.51/0.73     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.51/0.73       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.51/0.73  thf('37', plain,
% 0.51/0.73      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.51/0.73         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.51/0.73           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.51/0.73      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.51/0.73  thf('38', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.51/0.73           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['36', '37'])).
% 0.51/0.73  thf('39', plain,
% 0.51/0.73      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.73  thf(t5_boole, axiom,
% 0.51/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.51/0.73  thf('40', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.51/0.73      inference('cnf', [status(esa)], [t5_boole])).
% 0.51/0.73  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['39', '40'])).
% 0.51/0.73  thf('42', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.73      inference('demod', [status(thm)], ['38', '41'])).
% 0.51/0.73  thf('43', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['35', '42'])).
% 0.51/0.73  thf('44', plain,
% 0.51/0.73      (((sk_B_1) = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['34', '43'])).
% 0.51/0.73  thf(t93_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( k2_xboole_0 @ A @ B ) =
% 0.51/0.73       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.51/0.73  thf('45', plain,
% 0.51/0.73      (![X18 : $i, X19 : $i]:
% 0.51/0.73         ((k2_xboole_0 @ X18 @ X19)
% 0.51/0.73           = (k2_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 0.51/0.73              (k3_xboole_0 @ X18 @ X19)))),
% 0.51/0.73      inference('cnf', [status(esa)], [t93_xboole_1])).
% 0.51/0.73  thf('46', plain,
% 0.51/0.73      (![X54 : $i, X55 : $i]:
% 0.51/0.73         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.51/0.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.51/0.73  thf('47', plain,
% 0.51/0.73      (![X54 : $i, X55 : $i]:
% 0.51/0.73         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.51/0.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.51/0.73  thf('48', plain,
% 0.51/0.73      (![X18 : $i, X19 : $i]:
% 0.51/0.73         ((k3_tarski @ (k2_tarski @ X18 @ X19))
% 0.51/0.73           = (k3_tarski @ 
% 0.51/0.73              (k2_tarski @ (k5_xboole_0 @ X18 @ X19) @ 
% 0.51/0.73               (k3_xboole_0 @ X18 @ X19))))),
% 0.51/0.73      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.51/0.73  thf('49', plain,
% 0.51/0.73      (((k3_tarski @ (k2_tarski @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.51/0.73         = (k3_tarski @ 
% 0.51/0.73            (k2_tarski @ sk_B_1 @ 
% 0.51/0.73             (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)))))),
% 0.51/0.73      inference('sup+', [status(thm)], ['44', '48'])).
% 0.51/0.73  thf('50', plain,
% 0.51/0.73      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.51/0.73  thf('51', plain,
% 0.51/0.73      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.51/0.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.51/0.73  thf('52', plain,
% 0.51/0.73      (![X9 : $i, X10 : $i]:
% 0.51/0.73         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.51/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.51/0.73  thf('53', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.51/0.73           = (k4_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['51', '52'])).
% 0.51/0.73  thf('54', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.73  thf('55', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.51/0.73           = (k4_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('demod', [status(thm)], ['53', '54'])).
% 0.51/0.73  thf('56', plain,
% 0.51/0.73      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.51/0.73         = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['50', '55'])).
% 0.51/0.73  thf('57', plain,
% 0.51/0.73      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.51/0.73  thf('58', plain,
% 0.51/0.73      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.51/0.73         = (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.51/0.73      inference('demod', [status(thm)], ['56', '57'])).
% 0.51/0.73  thf(t94_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( k2_xboole_0 @ A @ B ) =
% 0.51/0.73       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.51/0.73  thf('59', plain,
% 0.51/0.73      (![X20 : $i, X21 : $i]:
% 0.51/0.73         ((k2_xboole_0 @ X20 @ X21)
% 0.51/0.73           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.51/0.73              (k3_xboole_0 @ X20 @ X21)))),
% 0.51/0.73      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.51/0.73  thf('60', plain,
% 0.51/0.73      (![X54 : $i, X55 : $i]:
% 0.51/0.73         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.51/0.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.51/0.73  thf('61', plain,
% 0.51/0.73      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.51/0.73         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.51/0.73           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.51/0.73      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.51/0.73  thf('62', plain,
% 0.51/0.73      (![X20 : $i, X21 : $i]:
% 0.51/0.73         ((k3_tarski @ (k2_tarski @ X20 @ X21))
% 0.51/0.73           = (k5_xboole_0 @ X20 @ 
% 0.51/0.73              (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X20 @ X21))))),
% 0.51/0.73      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.51/0.73  thf('63', plain,
% 0.51/0.73      (((k3_tarski @ (k2_tarski @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.51/0.73         = (k5_xboole_0 @ sk_A @ 
% 0.51/0.73            (k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ 
% 0.51/0.73             (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.51/0.73      inference('sup+', [status(thm)], ['58', '62'])).
% 0.51/0.73  thf('64', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.51/0.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.51/0.73  thf('65', plain,
% 0.51/0.73      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.73  thf('66', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['39', '40'])).
% 0.51/0.73  thf('67', plain,
% 0.51/0.73      (((k3_tarski @ (k2_tarski @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.51/0.73         = (sk_A))),
% 0.51/0.73      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 0.51/0.73  thf('68', plain,
% 0.51/0.73      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.51/0.73         = (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.51/0.73      inference('demod', [status(thm)], ['56', '57'])).
% 0.51/0.73  thf('69', plain,
% 0.51/0.73      (((sk_A)
% 0.51/0.73         = (k3_tarski @ (k2_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.51/0.73      inference('demod', [status(thm)], ['49', '67', '68'])).
% 0.51/0.73  thf('70', plain,
% 0.51/0.73      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_A))),
% 0.51/0.73      inference('demod', [status(thm)], ['17', '69'])).
% 0.51/0.73  thf('71', plain,
% 0.51/0.73      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.51/0.73         != (k2_subset_1 @ sk_A))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.51/0.73  thf('72', plain, (![X59 : $i]: ((k2_subset_1 @ X59) = (X59))),
% 0.51/0.73      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.51/0.73  thf('73', plain,
% 0.51/0.73      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) != (sk_A))),
% 0.51/0.73      inference('demod', [status(thm)], ['71', '72'])).
% 0.51/0.73  thf('74', plain, ($false),
% 0.51/0.73      inference('simplify_reflect-', [status(thm)], ['70', '73'])).
% 0.51/0.73  
% 0.51/0.73  % SZS output end Refutation
% 0.51/0.73  
% 0.51/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
