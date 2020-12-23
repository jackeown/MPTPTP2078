%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q8uhlTKE2x

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:51 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 133 expanded)
%              Number of leaves         :   37 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  626 ( 966 expanded)
%              Number of equality atoms :   58 (  85 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X60: $i,X61: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X60 @ X61 ) @ ( k1_zfmisc_1 @ X60 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X58: $i,X59: $i] :
      ( ( ( k3_subset_1 @ X58 @ X59 )
        = ( k4_xboole_0 @ X58 @ X59 ) )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
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

thf('9',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('10',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X64 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X64 ) )
      | ( ( k4_subset_1 @ X64 @ X63 @ X65 )
        = ( k3_tarski @ ( k2_tarski @ X63 @ X65 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ X55 )
      | ( r2_hidden @ X54 @ X55 )
      | ( v1_xboole_0 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X62: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('17',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('18',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ X50 @ X49 )
      | ( r1_tarski @ X50 @ X48 )
      | ( X49
       != ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('19',plain,(
    ! [X48: $i,X50: $i] :
      ( ( r1_tarski @ X50 @ X48 )
      | ~ ( r2_hidden @ X50 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['17','19'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k5_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('24',plain,(
    r1_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('28',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('37',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['31','32','33','36','41'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['42','49'])).

thf('51',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['12','50'])).

thf('52',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('53',plain,(
    ! [X57: $i] :
      ( ( k2_subset_1 @ X57 )
      = X57 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('54',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('56',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q8uhlTKE2x
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:14:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 308 iterations in 0.061s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.50  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.19/0.50  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(t25_subset_1, conjecture,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.50       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.19/0.50         ( k2_subset_1 @ A ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i]:
% 0.19/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.50          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.19/0.50            ( k2_subset_1 @ A ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.19/0.50  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(dt_k3_subset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.50       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (![X60 : $i, X61 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (k3_subset_1 @ X60 @ X61) @ (k1_zfmisc_1 @ X60))
% 0.19/0.50          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X60)))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d5_subset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.50       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X58 : $i, X59 : $i]:
% 0.19/0.50         (((k3_subset_1 @ X58 @ X59) = (k4_xboole_0 @ X58 @ X59))
% 0.19/0.50          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ X58)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['2', '5'])).
% 0.19/0.50  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(redefinition_k4_subset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.19/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.50       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X64))
% 0.19/0.50          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64))
% 0.19/0.50          | ((k4_subset_1 @ X64 @ X63 @ X65) = (k2_xboole_0 @ X63 @ X65)))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.19/0.50  thf(l51_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X52 : $i, X53 : $i]:
% 0.19/0.50         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.19/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X64))
% 0.19/0.50          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64))
% 0.19/0.50          | ((k4_subset_1 @ X64 @ X63 @ X65)
% 0.19/0.50              = (k3_tarski @ (k2_tarski @ X63 @ X65))))),
% 0.19/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 0.19/0.50            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['7', '10'])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.19/0.50         = (k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['6', '11'])).
% 0.19/0.50  thf('13', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d2_subset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( v1_xboole_0 @ A ) =>
% 0.19/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.19/0.50       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X54 : $i, X55 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X54 @ X55)
% 0.19/0.50          | (r2_hidden @ X54 @ X55)
% 0.19/0.50          | (v1_xboole_0 @ X55))),
% 0.19/0.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.50        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf(fc1_subset_1, axiom,
% 0.19/0.50    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.50  thf('16', plain, (![X62 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X62))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.19/0.50  thf('17', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.50      inference('clc', [status(thm)], ['15', '16'])).
% 0.19/0.50  thf(d1_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.19/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X50 @ X49)
% 0.19/0.50          | (r1_tarski @ X50 @ X48)
% 0.19/0.50          | ((X49) != (k1_zfmisc_1 @ X48)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X48 : $i, X50 : $i]:
% 0.19/0.50         ((r1_tarski @ X50 @ X48) | ~ (r2_hidden @ X50 @ (k1_zfmisc_1 @ X48)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['18'])).
% 0.19/0.50  thf('20', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.50      inference('sup-', [status(thm)], ['17', '19'])).
% 0.19/0.50  thf(t28_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i]:
% 0.19/0.50         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.19/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.50  thf('22', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.50  thf(l97_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      (![X7 : $i, X8 : $i]:
% 0.19/0.50         (r1_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ (k5_xboole_0 @ X7 @ X8))),
% 0.19/0.50      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.19/0.50  thf('24', plain, ((r1_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_A))),
% 0.19/0.50      inference('sup+', [status(thm)], ['22', '23'])).
% 0.19/0.50  thf(d7_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.19/0.50       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (![X4 : $i, X5 : $i]:
% 0.19/0.50         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.50  thf(t94_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k2_xboole_0 @ A @ B ) =
% 0.19/0.50       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X18 : $i, X19 : $i]:
% 0.19/0.50         ((k2_xboole_0 @ X18 @ X19)
% 0.19/0.50           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 0.19/0.50              (k3_xboole_0 @ X18 @ X19)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (![X52 : $i, X53 : $i]:
% 0.19/0.50         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.19/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.50  thf(t91_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.19/0.50       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.50         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.19/0.50           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.19/0.50  thf('30', plain,
% 0.19/0.50      (![X18 : $i, X19 : $i]:
% 0.19/0.50         ((k3_tarski @ (k2_tarski @ X18 @ X19))
% 0.19/0.50           = (k5_xboole_0 @ X18 @ 
% 0.19/0.50              (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X18 @ X19))))),
% 0.19/0.50      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      (((k3_tarski @ (k2_tarski @ sk_B @ (k5_xboole_0 @ sk_B @ sk_A)))
% 0.19/0.50         = (k5_xboole_0 @ sk_B @ 
% 0.19/0.50            (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_A) @ k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['26', '30'])).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.50         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.19/0.50           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.19/0.50  thf(commutativity_k5_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.50  thf('34', plain,
% 0.19/0.50      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.50  thf(t5_boole, axiom,
% 0.19/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.50  thf('35', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.19/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.50  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['34', '35'])).
% 0.19/0.50  thf(t92_xboole_1, axiom,
% 0.19/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.50  thf('37', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.50  thf('38', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.50         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.19/0.50           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.19/0.50           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['37', '38'])).
% 0.19/0.50  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['34', '35'])).
% 0.19/0.50  thf('41', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['39', '40'])).
% 0.19/0.50  thf('42', plain,
% 0.19/0.50      (((k3_tarski @ (k2_tarski @ sk_B @ (k5_xboole_0 @ sk_B @ sk_A))) = (sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['31', '32', '33', '36', '41'])).
% 0.19/0.50  thf('43', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.50  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.50  thf('44', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.50  thf(t100_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.50  thf('45', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i]:
% 0.19/0.50         ((k4_xboole_0 @ X9 @ X10)
% 0.19/0.50           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.50  thf('46', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((k4_xboole_0 @ X0 @ X1)
% 0.19/0.50           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['44', '45'])).
% 0.19/0.50  thf('47', plain,
% 0.19/0.50      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.50      inference('sup+', [status(thm)], ['43', '46'])).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.50  thf('49', plain,
% 0.19/0.50      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['47', '48'])).
% 0.19/0.50  thf('50', plain,
% 0.19/0.50      (((k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))) = (sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['42', '49'])).
% 0.19/0.50  thf('51', plain,
% 0.19/0.50      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['12', '50'])).
% 0.19/0.50  thf('52', plain,
% 0.19/0.50      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.50         != (k2_subset_1 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.50  thf('53', plain, (![X57 : $i]: ((k2_subset_1 @ X57) = (X57))),
% 0.19/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.50  thf('54', plain,
% 0.19/0.50      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['52', '53'])).
% 0.19/0.50  thf('55', plain,
% 0.19/0.50      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.50  thf('56', plain,
% 0.19/0.50      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['54', '55'])).
% 0.19/0.50  thf('57', plain, ($false),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['51', '56'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
