%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vdz9jzsrD4

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:51 EST 2020

% Result     : Theorem 18.13s
% Output     : Refutation 18.13s
% Verified   : 
% Statistics : Number of formulae       :  204 (1206 expanded)
%              Number of leaves         :   37 ( 397 expanded)
%              Depth                    :   29
%              Number of atoms          : 1546 (8990 expanded)
%              Number of equality atoms :  138 ( 856 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ X61 )
      | ( r2_hidden @ X60 @ X61 )
      | ( v1_xboole_0 @ X61 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X66: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X56 @ X55 )
      | ( r1_tarski @ X56 @ X54 )
      | ( X55
       != ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X54: $i,X56: $i] :
      ( ( r1_tarski @ X56 @ X54 )
      | ~ ( r2_hidden @ X56 @ ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X64: $i,X65: $i] :
      ( ( ( k3_subset_1 @ X64 @ X65 )
        = ( k4_xboole_0 @ X64 @ X65 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('36',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( r1_tarski @ X53 @ X54 )
      | ( r2_hidden @ X53 @ X55 )
      | ( X55
       != ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('37',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r2_hidden @ X53 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( r1_tarski @ X53 @ X54 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( r2_hidden @ X60 @ X61 )
      | ( m1_subset_1 @ X60 @ X61 )
      | ( v1_xboole_0 @ X61 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X66: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X64: $i,X65: $i] :
      ( ( ( k3_subset_1 @ X64 @ X65 )
        = ( k4_xboole_0 @ X64 @ X65 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','45'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('47',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('54',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('61',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('62',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('65',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','68'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('70',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('73',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','75'])).

thf('77',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('78',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('79',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X12 @ X14 ) @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('84',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('85',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('91',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('93',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('95',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('97',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','45'])).

thf('99',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
    = ( k3_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['63','66'])).

thf('101',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['90','101'])).

thf('103',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['90','101'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['89','102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('107',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('111',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','112'])).

thf('117',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['114','119'])).

thf('121',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['113','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','124'])).

thf('126',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('127',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','125','126','127','128'])).

thf('130',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['77','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('132',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['131','134'])).

thf('136',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['130','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('138',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['136','137'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('139',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('140',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X58 @ X59 ) )
      = ( k2_xboole_0 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('141',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('143',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['138','143'])).

thf('145',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['76','144'])).

thf('146',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('147',plain,(
    ! [X63: $i] :
      ( ( k2_subset_1 @ X63 )
      = X63 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('148',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('150',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('151',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r2_hidden @ X53 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( r1_tarski @ X53 @ X54 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('153',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( r2_hidden @ X60 @ X61 )
      | ( m1_subset_1 @ X60 @ X61 )
      | ( v1_xboole_0 @ X61 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('155',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X66: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('157',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('159',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X68 ) )
      | ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ X68 ) )
      | ( ( k4_subset_1 @ X68 @ X67 @ X69 )
        = ( k2_xboole_0 @ X67 @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('160',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X58 @ X59 ) )
      = ( k2_xboole_0 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('161',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X68 ) )
      | ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ X68 ) )
      | ( ( k4_subset_1 @ X68 @ X67 @ X69 )
        = ( k3_tarski @ ( k2_tarski @ X67 @ X69 ) ) ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['158','161'])).

thf('163',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['157','162'])).

thf('164',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
 != sk_A ),
    inference(demod,[status(thm)],['148','163'])).

thf('165',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['145','164'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vdz9jzsrD4
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:57:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 18.13/18.38  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 18.13/18.38  % Solved by: fo/fo7.sh
% 18.13/18.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.13/18.38  % done 13121 iterations in 17.921s
% 18.13/18.38  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 18.13/18.38  % SZS output start Refutation
% 18.13/18.38  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 18.13/18.38  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 18.13/18.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 18.13/18.38  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 18.13/18.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 18.13/18.38  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 18.13/18.38  thf(sk_A_type, type, sk_A: $i).
% 18.13/18.38  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 18.13/18.38  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 18.13/18.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 18.13/18.38  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 18.13/18.38  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 18.13/18.38  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 18.13/18.38  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 18.13/18.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 18.13/18.39  thf(sk_B_type, type, sk_B: $i).
% 18.13/18.39  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 18.13/18.39  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 18.13/18.39  thf(t25_subset_1, conjecture,
% 18.13/18.39    (![A:$i,B:$i]:
% 18.13/18.39     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 18.13/18.39       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 18.13/18.39         ( k2_subset_1 @ A ) ) ))).
% 18.13/18.39  thf(zf_stmt_0, negated_conjecture,
% 18.13/18.39    (~( ![A:$i,B:$i]:
% 18.13/18.39        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 18.13/18.39          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 18.13/18.39            ( k2_subset_1 @ A ) ) ) )),
% 18.13/18.39    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 18.13/18.39  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 18.13/18.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.13/18.39  thf(d2_subset_1, axiom,
% 18.13/18.39    (![A:$i,B:$i]:
% 18.13/18.39     ( ( ( v1_xboole_0 @ A ) =>
% 18.13/18.39         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 18.13/18.39       ( ( ~( v1_xboole_0 @ A ) ) =>
% 18.13/18.39         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 18.13/18.39  thf('1', plain,
% 18.13/18.39      (![X60 : $i, X61 : $i]:
% 18.13/18.39         (~ (m1_subset_1 @ X60 @ X61)
% 18.13/18.39          | (r2_hidden @ X60 @ X61)
% 18.13/18.39          | (v1_xboole_0 @ X61))),
% 18.13/18.39      inference('cnf', [status(esa)], [d2_subset_1])).
% 18.13/18.39  thf('2', plain,
% 18.13/18.39      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 18.13/18.39        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 18.13/18.39      inference('sup-', [status(thm)], ['0', '1'])).
% 18.13/18.39  thf(fc1_subset_1, axiom,
% 18.13/18.39    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 18.13/18.39  thf('3', plain, (![X66 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X66))),
% 18.13/18.39      inference('cnf', [status(esa)], [fc1_subset_1])).
% 18.13/18.39  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 18.13/18.39      inference('clc', [status(thm)], ['2', '3'])).
% 18.13/18.39  thf(d1_zfmisc_1, axiom,
% 18.13/18.39    (![A:$i,B:$i]:
% 18.13/18.39     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 18.13/18.39       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 18.13/18.39  thf('5', plain,
% 18.13/18.39      (![X54 : $i, X55 : $i, X56 : $i]:
% 18.13/18.39         (~ (r2_hidden @ X56 @ X55)
% 18.13/18.39          | (r1_tarski @ X56 @ X54)
% 18.13/18.39          | ((X55) != (k1_zfmisc_1 @ X54)))),
% 18.13/18.39      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 18.13/18.39  thf('6', plain,
% 18.13/18.39      (![X54 : $i, X56 : $i]:
% 18.13/18.39         ((r1_tarski @ X56 @ X54) | ~ (r2_hidden @ X56 @ (k1_zfmisc_1 @ X54)))),
% 18.13/18.39      inference('simplify', [status(thm)], ['5'])).
% 18.13/18.39  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 18.13/18.39      inference('sup-', [status(thm)], ['4', '6'])).
% 18.13/18.39  thf(t28_xboole_1, axiom,
% 18.13/18.39    (![A:$i,B:$i]:
% 18.13/18.39     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 18.13/18.39  thf('8', plain,
% 18.13/18.39      (![X15 : $i, X16 : $i]:
% 18.13/18.39         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 18.13/18.39      inference('cnf', [status(esa)], [t28_xboole_1])).
% 18.13/18.39  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 18.13/18.39      inference('sup-', [status(thm)], ['7', '8'])).
% 18.13/18.39  thf(commutativity_k3_xboole_0, axiom,
% 18.13/18.39    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 18.13/18.39  thf('10', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 18.13/18.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 18.13/18.39  thf(t100_xboole_1, axiom,
% 18.13/18.39    (![A:$i,B:$i]:
% 18.13/18.39     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 18.13/18.39  thf('11', plain,
% 18.13/18.39      (![X10 : $i, X11 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ X10 @ X11)
% 18.13/18.39           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 18.13/18.39      inference('cnf', [status(esa)], [t100_xboole_1])).
% 18.13/18.39  thf('12', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ X0 @ X1)
% 18.13/18.39           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 18.13/18.39      inference('sup+', [status(thm)], ['10', '11'])).
% 18.13/18.39  thf('13', plain,
% 18.13/18.39      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 18.13/18.39      inference('sup+', [status(thm)], ['9', '12'])).
% 18.13/18.39  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 18.13/18.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.13/18.39  thf(d5_subset_1, axiom,
% 18.13/18.39    (![A:$i,B:$i]:
% 18.13/18.39     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 18.13/18.39       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 18.13/18.39  thf('15', plain,
% 18.13/18.39      (![X64 : $i, X65 : $i]:
% 18.13/18.39         (((k3_subset_1 @ X64 @ X65) = (k4_xboole_0 @ X64 @ X65))
% 18.13/18.39          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64)))),
% 18.13/18.39      inference('cnf', [status(esa)], [d5_subset_1])).
% 18.13/18.39  thf('16', plain,
% 18.13/18.39      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 18.13/18.39      inference('sup-', [status(thm)], ['14', '15'])).
% 18.13/18.39  thf(commutativity_k5_xboole_0, axiom,
% 18.13/18.39    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 18.13/18.39  thf('17', plain,
% 18.13/18.39      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 18.13/18.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 18.13/18.39  thf('18', plain,
% 18.13/18.39      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 18.13/18.39      inference('demod', [status(thm)], ['13', '16', '17'])).
% 18.13/18.39  thf(t2_boole, axiom,
% 18.13/18.39    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 18.13/18.39  thf('19', plain,
% 18.13/18.39      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 18.13/18.39      inference('cnf', [status(esa)], [t2_boole])).
% 18.13/18.39  thf('20', plain,
% 18.13/18.39      (![X10 : $i, X11 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ X10 @ X11)
% 18.13/18.39           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 18.13/18.39      inference('cnf', [status(esa)], [t100_xboole_1])).
% 18.13/18.39  thf('21', plain,
% 18.13/18.39      (![X0 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 18.13/18.39      inference('sup+', [status(thm)], ['19', '20'])).
% 18.13/18.39  thf(t5_boole, axiom,
% 18.13/18.39    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 18.13/18.39  thf('22', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 18.13/18.39      inference('cnf', [status(esa)], [t5_boole])).
% 18.13/18.39  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 18.13/18.39      inference('sup+', [status(thm)], ['21', '22'])).
% 18.13/18.39  thf(t36_xboole_1, axiom,
% 18.13/18.39    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 18.13/18.39  thf('24', plain,
% 18.13/18.39      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 18.13/18.39      inference('cnf', [status(esa)], [t36_xboole_1])).
% 18.13/18.39  thf('25', plain,
% 18.13/18.39      (![X15 : $i, X16 : $i]:
% 18.13/18.39         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 18.13/18.39      inference('cnf', [status(esa)], [t28_xboole_1])).
% 18.13/18.39  thf('26', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 18.13/18.39           = (k4_xboole_0 @ X0 @ X1))),
% 18.13/18.39      inference('sup-', [status(thm)], ['24', '25'])).
% 18.13/18.39  thf('27', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 18.13/18.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 18.13/18.39  thf('28', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 18.13/18.39           = (k4_xboole_0 @ X0 @ X1))),
% 18.13/18.39      inference('demod', [status(thm)], ['26', '27'])).
% 18.13/18.39  thf('29', plain,
% 18.13/18.39      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 18.13/18.39      inference('sup+', [status(thm)], ['23', '28'])).
% 18.13/18.39  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 18.13/18.39      inference('sup+', [status(thm)], ['21', '22'])).
% 18.13/18.39  thf('31', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 18.13/18.39      inference('demod', [status(thm)], ['29', '30'])).
% 18.13/18.39  thf('32', plain,
% 18.13/18.39      (![X10 : $i, X11 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ X10 @ X11)
% 18.13/18.39           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 18.13/18.39      inference('cnf', [status(esa)], [t100_xboole_1])).
% 18.13/18.39  thf('33', plain,
% 18.13/18.39      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 18.13/18.39      inference('sup+', [status(thm)], ['31', '32'])).
% 18.13/18.39  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 18.13/18.39      inference('sup+', [status(thm)], ['21', '22'])).
% 18.13/18.39  thf('35', plain,
% 18.13/18.39      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 18.13/18.39      inference('cnf', [status(esa)], [t36_xboole_1])).
% 18.13/18.39  thf('36', plain,
% 18.13/18.39      (![X53 : $i, X54 : $i, X55 : $i]:
% 18.13/18.39         (~ (r1_tarski @ X53 @ X54)
% 18.13/18.39          | (r2_hidden @ X53 @ X55)
% 18.13/18.39          | ((X55) != (k1_zfmisc_1 @ X54)))),
% 18.13/18.39      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 18.13/18.39  thf('37', plain,
% 18.13/18.39      (![X53 : $i, X54 : $i]:
% 18.13/18.39         ((r2_hidden @ X53 @ (k1_zfmisc_1 @ X54)) | ~ (r1_tarski @ X53 @ X54))),
% 18.13/18.39      inference('simplify', [status(thm)], ['36'])).
% 18.13/18.39  thf('38', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         (r2_hidden @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 18.13/18.39      inference('sup-', [status(thm)], ['35', '37'])).
% 18.13/18.39  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 18.13/18.39      inference('sup+', [status(thm)], ['34', '38'])).
% 18.13/18.39  thf('40', plain,
% 18.13/18.39      (![X60 : $i, X61 : $i]:
% 18.13/18.39         (~ (r2_hidden @ X60 @ X61)
% 18.13/18.39          | (m1_subset_1 @ X60 @ X61)
% 18.13/18.39          | (v1_xboole_0 @ X61))),
% 18.13/18.39      inference('cnf', [status(esa)], [d2_subset_1])).
% 18.13/18.39  thf('41', plain,
% 18.13/18.39      (![X0 : $i]:
% 18.13/18.39         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 18.13/18.39          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 18.13/18.39      inference('sup-', [status(thm)], ['39', '40'])).
% 18.13/18.39  thf('42', plain, (![X66 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X66))),
% 18.13/18.39      inference('cnf', [status(esa)], [fc1_subset_1])).
% 18.13/18.39  thf('43', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 18.13/18.39      inference('clc', [status(thm)], ['41', '42'])).
% 18.13/18.39  thf('44', plain,
% 18.13/18.39      (![X64 : $i, X65 : $i]:
% 18.13/18.39         (((k3_subset_1 @ X64 @ X65) = (k4_xboole_0 @ X64 @ X65))
% 18.13/18.39          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64)))),
% 18.13/18.39      inference('cnf', [status(esa)], [d5_subset_1])).
% 18.13/18.39  thf('45', plain,
% 18.13/18.39      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 18.13/18.39      inference('sup-', [status(thm)], ['43', '44'])).
% 18.13/18.39  thf('46', plain,
% 18.13/18.39      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 18.13/18.39      inference('demod', [status(thm)], ['33', '45'])).
% 18.13/18.39  thf(d5_xboole_0, axiom,
% 18.13/18.39    (![A:$i,B:$i,C:$i]:
% 18.13/18.39     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 18.13/18.39       ( ![D:$i]:
% 18.13/18.39         ( ( r2_hidden @ D @ C ) <=>
% 18.13/18.39           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 18.13/18.39  thf('47', plain,
% 18.13/18.39      (![X5 : $i, X6 : $i, X9 : $i]:
% 18.13/18.39         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 18.13/18.39          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 18.13/18.39          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 18.13/18.39      inference('cnf', [status(esa)], [d5_xboole_0])).
% 18.13/18.39  thf('48', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 18.13/18.39           = (k4_xboole_0 @ X0 @ X1))),
% 18.13/18.39      inference('demod', [status(thm)], ['26', '27'])).
% 18.13/18.39  thf('49', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 18.13/18.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 18.13/18.39  thf('50', plain,
% 18.13/18.39      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 18.13/18.39      inference('cnf', [status(esa)], [t2_boole])).
% 18.13/18.39  thf('51', plain,
% 18.13/18.39      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 18.13/18.39      inference('sup+', [status(thm)], ['49', '50'])).
% 18.13/18.39  thf('52', plain,
% 18.13/18.39      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 18.13/18.39      inference('sup+', [status(thm)], ['48', '51'])).
% 18.13/18.39  thf('53', plain,
% 18.13/18.39      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 18.13/18.39         (~ (r2_hidden @ X8 @ X7)
% 18.13/18.39          | ~ (r2_hidden @ X8 @ X6)
% 18.13/18.39          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 18.13/18.39      inference('cnf', [status(esa)], [d5_xboole_0])).
% 18.13/18.39  thf('54', plain,
% 18.13/18.39      (![X5 : $i, X6 : $i, X8 : $i]:
% 18.13/18.39         (~ (r2_hidden @ X8 @ X6)
% 18.13/18.39          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 18.13/18.39      inference('simplify', [status(thm)], ['53'])).
% 18.13/18.39  thf('55', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 18.13/18.39      inference('sup-', [status(thm)], ['52', '54'])).
% 18.13/18.39  thf('56', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 18.13/18.39      inference('condensation', [status(thm)], ['55'])).
% 18.13/18.39  thf('57', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 18.13/18.39          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 18.13/18.39      inference('sup-', [status(thm)], ['47', '56'])).
% 18.13/18.39  thf('58', plain,
% 18.13/18.39      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 18.13/18.39      inference('sup+', [status(thm)], ['48', '51'])).
% 18.13/18.39  thf('59', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 18.13/18.39          | ((X1) = (k1_xboole_0)))),
% 18.13/18.39      inference('demod', [status(thm)], ['57', '58'])).
% 18.13/18.39  thf('60', plain,
% 18.13/18.39      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 18.13/18.39      inference('sup-', [status(thm)], ['43', '44'])).
% 18.13/18.39  thf('61', plain,
% 18.13/18.39      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 18.13/18.39         (~ (r2_hidden @ X8 @ X7)
% 18.13/18.39          | (r2_hidden @ X8 @ X5)
% 18.13/18.39          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 18.13/18.39      inference('cnf', [status(esa)], [d5_xboole_0])).
% 18.13/18.39  thf('62', plain,
% 18.13/18.39      (![X5 : $i, X6 : $i, X8 : $i]:
% 18.13/18.39         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 18.13/18.39      inference('simplify', [status(thm)], ['61'])).
% 18.13/18.39  thf('63', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         (~ (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 18.13/18.39      inference('sup-', [status(thm)], ['60', '62'])).
% 18.13/18.39  thf('64', plain,
% 18.13/18.39      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 18.13/18.39      inference('sup-', [status(thm)], ['43', '44'])).
% 18.13/18.39  thf('65', plain,
% 18.13/18.39      (![X5 : $i, X6 : $i, X8 : $i]:
% 18.13/18.39         (~ (r2_hidden @ X8 @ X6)
% 18.13/18.39          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 18.13/18.39      inference('simplify', [status(thm)], ['53'])).
% 18.13/18.39  thf('66', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         (~ (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ X0))
% 18.13/18.39          | ~ (r2_hidden @ X1 @ X0))),
% 18.13/18.39      inference('sup-', [status(thm)], ['64', '65'])).
% 18.13/18.39  thf('67', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ X0))),
% 18.13/18.39      inference('clc', [status(thm)], ['63', '66'])).
% 18.13/18.39  thf('68', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 18.13/18.39      inference('sup-', [status(thm)], ['59', '67'])).
% 18.13/18.39  thf('69', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 18.13/18.39      inference('demod', [status(thm)], ['46', '68'])).
% 18.13/18.39  thf(t91_xboole_1, axiom,
% 18.13/18.39    (![A:$i,B:$i,C:$i]:
% 18.13/18.39     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 18.13/18.39       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 18.13/18.39  thf('70', plain,
% 18.13/18.39      (![X21 : $i, X22 : $i, X23 : $i]:
% 18.13/18.39         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 18.13/18.39           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 18.13/18.39      inference('cnf', [status(esa)], [t91_xboole_1])).
% 18.13/18.39  thf('71', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 18.13/18.39           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 18.13/18.39      inference('sup+', [status(thm)], ['69', '70'])).
% 18.13/18.39  thf('72', plain,
% 18.13/18.39      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 18.13/18.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 18.13/18.39  thf('73', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 18.13/18.39      inference('cnf', [status(esa)], [t5_boole])).
% 18.13/18.39  thf('74', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 18.13/18.39      inference('sup+', [status(thm)], ['72', '73'])).
% 18.13/18.39  thf('75', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 18.13/18.39      inference('demod', [status(thm)], ['71', '74'])).
% 18.13/18.39  thf('76', plain,
% 18.13/18.39      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 18.13/18.39      inference('sup+', [status(thm)], ['18', '75'])).
% 18.13/18.39  thf('77', plain,
% 18.13/18.39      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 18.13/18.39      inference('sup-', [status(thm)], ['14', '15'])).
% 18.13/18.39  thf('78', plain,
% 18.13/18.39      (![X10 : $i, X11 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ X10 @ X11)
% 18.13/18.39           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 18.13/18.39      inference('cnf', [status(esa)], [t100_xboole_1])).
% 18.13/18.39  thf(t112_xboole_1, axiom,
% 18.13/18.39    (![A:$i,B:$i,C:$i]:
% 18.13/18.39     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 18.13/18.39       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 18.13/18.39  thf('79', plain,
% 18.13/18.39      (![X12 : $i, X13 : $i, X14 : $i]:
% 18.13/18.39         ((k5_xboole_0 @ (k3_xboole_0 @ X12 @ X14) @ (k3_xboole_0 @ X13 @ X14))
% 18.13/18.39           = (k3_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14))),
% 18.13/18.39      inference('cnf', [status(esa)], [t112_xboole_1])).
% 18.13/18.39  thf('80', plain,
% 18.13/18.39      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 18.13/18.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 18.13/18.39  thf('81', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.13/18.39         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0))
% 18.13/18.39           = (k3_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0))),
% 18.13/18.39      inference('sup+', [status(thm)], ['79', '80'])).
% 18.13/18.39  thf('82', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 18.13/18.39           = (k3_xboole_0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) @ X0))),
% 18.13/18.39      inference('sup+', [status(thm)], ['78', '81'])).
% 18.13/18.39  thf('83', plain,
% 18.13/18.39      (![X5 : $i, X6 : $i, X9 : $i]:
% 18.13/18.39         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 18.13/18.39          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 18.13/18.39          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 18.13/18.39      inference('cnf', [status(esa)], [d5_xboole_0])).
% 18.13/18.39  thf('84', plain,
% 18.13/18.39      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 18.13/18.39      inference('sup-', [status(thm)], ['14', '15'])).
% 18.13/18.39  thf('85', plain,
% 18.13/18.39      (![X5 : $i, X6 : $i, X8 : $i]:
% 18.13/18.39         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 18.13/18.39      inference('simplify', [status(thm)], ['61'])).
% 18.13/18.39  thf('86', plain,
% 18.13/18.39      (![X0 : $i]:
% 18.13/18.39         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 18.13/18.39          | (r2_hidden @ X0 @ sk_A))),
% 18.13/18.39      inference('sup-', [status(thm)], ['84', '85'])).
% 18.13/18.39  thf('87', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((r2_hidden @ (sk_D @ X1 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ X1)
% 18.13/18.39          | ((X1) = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0))
% 18.13/18.39          | (r2_hidden @ (sk_D @ X1 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ sk_A))),
% 18.13/18.39      inference('sup-', [status(thm)], ['83', '86'])).
% 18.13/18.39  thf('88', plain,
% 18.13/18.39      (![X5 : $i, X6 : $i, X9 : $i]:
% 18.13/18.39         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 18.13/18.39          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 18.13/18.39          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 18.13/18.39      inference('cnf', [status(esa)], [d5_xboole_0])).
% 18.13/18.39  thf('89', plain,
% 18.13/18.39      (![X0 : $i]:
% 18.13/18.39         (((X0) = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 18.13/18.39          | (r2_hidden @ (sk_D @ X0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) @ X0)
% 18.13/18.39          | (r2_hidden @ (sk_D @ X0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) @ X0)
% 18.13/18.39          | ((X0) = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)))),
% 18.13/18.39      inference('sup-', [status(thm)], ['87', '88'])).
% 18.13/18.39  thf('90', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 18.13/18.39          | ((X1) = (k1_xboole_0)))),
% 18.13/18.39      inference('demod', [status(thm)], ['57', '58'])).
% 18.13/18.39  thf('91', plain,
% 18.13/18.39      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 18.13/18.39      inference('sup-', [status(thm)], ['14', '15'])).
% 18.13/18.39  thf('92', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 18.13/18.39           = (k4_xboole_0 @ X0 @ X1))),
% 18.13/18.39      inference('demod', [status(thm)], ['26', '27'])).
% 18.13/18.39  thf('93', plain,
% 18.13/18.39      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 18.13/18.39         = (k4_xboole_0 @ sk_A @ sk_B))),
% 18.13/18.39      inference('sup+', [status(thm)], ['91', '92'])).
% 18.13/18.39  thf('94', plain,
% 18.13/18.39      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 18.13/18.39      inference('sup-', [status(thm)], ['14', '15'])).
% 18.13/18.39  thf('95', plain,
% 18.13/18.39      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 18.13/18.39         = (k3_subset_1 @ sk_A @ sk_B))),
% 18.13/18.39      inference('demod', [status(thm)], ['93', '94'])).
% 18.13/18.39  thf('96', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ X0 @ X1)
% 18.13/18.39           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 18.13/18.39      inference('sup+', [status(thm)], ['10', '11'])).
% 18.13/18.39  thf('97', plain,
% 18.13/18.39      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)
% 18.13/18.39         = (k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 18.13/18.39            (k3_subset_1 @ sk_A @ sk_B)))),
% 18.13/18.39      inference('sup+', [status(thm)], ['95', '96'])).
% 18.13/18.39  thf('98', plain,
% 18.13/18.39      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 18.13/18.39      inference('demod', [status(thm)], ['33', '45'])).
% 18.13/18.39  thf('99', plain,
% 18.13/18.39      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)
% 18.13/18.39         = (k3_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 18.13/18.39            (k3_subset_1 @ sk_A @ sk_B)))),
% 18.13/18.39      inference('demod', [status(thm)], ['97', '98'])).
% 18.13/18.39  thf('100', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ X0))),
% 18.13/18.39      inference('clc', [status(thm)], ['63', '66'])).
% 18.13/18.39  thf('101', plain,
% 18.13/18.39      (![X0 : $i]:
% 18.13/18.39         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))),
% 18.13/18.39      inference('sup-', [status(thm)], ['99', '100'])).
% 18.13/18.39  thf('102', plain,
% 18.13/18.39      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A) = (k1_xboole_0))),
% 18.13/18.39      inference('sup-', [status(thm)], ['90', '101'])).
% 18.13/18.39  thf('103', plain,
% 18.13/18.39      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A) = (k1_xboole_0))),
% 18.13/18.39      inference('sup-', [status(thm)], ['90', '101'])).
% 18.13/18.39  thf('104', plain,
% 18.13/18.39      (![X0 : $i]:
% 18.13/18.39         (((X0) = (k1_xboole_0))
% 18.13/18.39          | (r2_hidden @ (sk_D @ X0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) @ X0)
% 18.13/18.39          | (r2_hidden @ (sk_D @ X0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) @ X0)
% 18.13/18.39          | ((X0) = (k1_xboole_0)))),
% 18.13/18.39      inference('demod', [status(thm)], ['89', '102', '103'])).
% 18.13/18.39  thf('105', plain,
% 18.13/18.39      (![X0 : $i]:
% 18.13/18.39         ((r2_hidden @ (sk_D @ X0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) @ X0)
% 18.13/18.39          | ((X0) = (k1_xboole_0)))),
% 18.13/18.39      inference('simplify', [status(thm)], ['104'])).
% 18.13/18.39  thf('106', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 18.13/18.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 18.13/18.39  thf('107', plain,
% 18.13/18.39      (![X10 : $i, X11 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ X10 @ X11)
% 18.13/18.39           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 18.13/18.39      inference('cnf', [status(esa)], [t100_xboole_1])).
% 18.13/18.39  thf('108', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 18.13/18.39      inference('demod', [status(thm)], ['71', '74'])).
% 18.13/18.39  thf('109', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k3_xboole_0 @ X1 @ X0)
% 18.13/18.39           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 18.13/18.39      inference('sup+', [status(thm)], ['107', '108'])).
% 18.13/18.39  thf('110', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 18.13/18.39           = (k4_xboole_0 @ X0 @ X1))),
% 18.13/18.39      inference('demod', [status(thm)], ['26', '27'])).
% 18.13/18.39  thf('111', plain,
% 18.13/18.39      (![X10 : $i, X11 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ X10 @ X11)
% 18.13/18.39           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 18.13/18.39      inference('cnf', [status(esa)], [t100_xboole_1])).
% 18.13/18.39  thf('112', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 18.13/18.39           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 18.13/18.39      inference('sup+', [status(thm)], ['110', '111'])).
% 18.13/18.39  thf('113', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 18.13/18.39           = (k3_xboole_0 @ X1 @ X0))),
% 18.13/18.39      inference('sup+', [status(thm)], ['109', '112'])).
% 18.13/18.39  thf('114', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 18.13/18.39           = (k4_xboole_0 @ X0 @ X1))),
% 18.13/18.39      inference('demod', [status(thm)], ['26', '27'])).
% 18.13/18.39  thf('115', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 18.13/18.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 18.13/18.39  thf('116', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 18.13/18.39           = (k3_xboole_0 @ X1 @ X0))),
% 18.13/18.39      inference('sup+', [status(thm)], ['109', '112'])).
% 18.13/18.39  thf('117', plain,
% 18.13/18.39      (![X5 : $i, X6 : $i, X8 : $i]:
% 18.13/18.39         (~ (r2_hidden @ X8 @ X6)
% 18.13/18.39          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 18.13/18.39      inference('simplify', [status(thm)], ['53'])).
% 18.13/18.39  thf('118', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.13/18.39         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 18.13/18.39          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 18.13/18.39      inference('sup-', [status(thm)], ['116', '117'])).
% 18.13/18.39  thf('119', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.13/18.39         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 18.13/18.39          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 18.13/18.39      inference('sup-', [status(thm)], ['115', '118'])).
% 18.13/18.39  thf('120', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.13/18.39         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 18.13/18.39          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 18.13/18.39      inference('sup-', [status(thm)], ['114', '119'])).
% 18.13/18.39  thf('121', plain,
% 18.13/18.39      (![X5 : $i, X6 : $i, X8 : $i]:
% 18.13/18.39         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 18.13/18.39      inference('simplify', [status(thm)], ['61'])).
% 18.13/18.39  thf('122', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.13/18.39         ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 18.13/18.39      inference('clc', [status(thm)], ['120', '121'])).
% 18.13/18.39  thf('123', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.13/18.39         ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 18.13/18.39      inference('sup-', [status(thm)], ['113', '122'])).
% 18.13/18.39  thf('124', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.13/18.39         ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 18.13/18.39      inference('sup-', [status(thm)], ['106', '123'])).
% 18.13/18.39  thf('125', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 18.13/18.39      inference('sup-', [status(thm)], ['105', '124'])).
% 18.13/18.39  thf('126', plain,
% 18.13/18.39      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 18.13/18.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 18.13/18.39  thf('127', plain,
% 18.13/18.39      (![X10 : $i, X11 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ X10 @ X11)
% 18.13/18.39           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 18.13/18.39      inference('cnf', [status(esa)], [t100_xboole_1])).
% 18.13/18.39  thf('128', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 18.13/18.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 18.13/18.39  thf('129', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 18.13/18.39      inference('demod', [status(thm)], ['82', '125', '126', '127', '128'])).
% 18.13/18.39  thf('130', plain,
% 18.13/18.39      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 18.13/18.39      inference('sup+', [status(thm)], ['77', '129'])).
% 18.13/18.39  thf('131', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ X0 @ X1)
% 18.13/18.39           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 18.13/18.39      inference('sup+', [status(thm)], ['10', '11'])).
% 18.13/18.39  thf('132', plain,
% 18.13/18.39      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 18.13/18.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 18.13/18.39  thf('133', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 18.13/18.39      inference('demod', [status(thm)], ['71', '74'])).
% 18.13/18.39  thf('134', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 18.13/18.39      inference('sup+', [status(thm)], ['132', '133'])).
% 18.13/18.39  thf('135', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((X1)
% 18.13/18.39           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 18.13/18.39      inference('sup+', [status(thm)], ['131', '134'])).
% 18.13/18.39  thf('136', plain,
% 18.13/18.39      (((k3_subset_1 @ sk_A @ sk_B)
% 18.13/18.39         = (k5_xboole_0 @ k1_xboole_0 @ 
% 18.13/18.39            (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 18.13/18.39      inference('sup+', [status(thm)], ['130', '135'])).
% 18.13/18.39  thf('137', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 18.13/18.39      inference('sup+', [status(thm)], ['72', '73'])).
% 18.13/18.39  thf('138', plain,
% 18.13/18.39      (((k3_subset_1 @ sk_A @ sk_B)
% 18.13/18.39         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 18.13/18.39      inference('demod', [status(thm)], ['136', '137'])).
% 18.13/18.39  thf(t94_xboole_1, axiom,
% 18.13/18.39    (![A:$i,B:$i]:
% 18.13/18.39     ( ( k2_xboole_0 @ A @ B ) =
% 18.13/18.39       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 18.13/18.39  thf('139', plain,
% 18.13/18.39      (![X24 : $i, X25 : $i]:
% 18.13/18.39         ((k2_xboole_0 @ X24 @ X25)
% 18.13/18.39           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 18.13/18.39              (k3_xboole_0 @ X24 @ X25)))),
% 18.13/18.39      inference('cnf', [status(esa)], [t94_xboole_1])).
% 18.13/18.39  thf(l51_zfmisc_1, axiom,
% 18.13/18.39    (![A:$i,B:$i]:
% 18.13/18.39     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 18.13/18.39  thf('140', plain,
% 18.13/18.39      (![X58 : $i, X59 : $i]:
% 18.13/18.39         ((k3_tarski @ (k2_tarski @ X58 @ X59)) = (k2_xboole_0 @ X58 @ X59))),
% 18.13/18.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 18.13/18.39  thf('141', plain,
% 18.13/18.39      (![X21 : $i, X22 : $i, X23 : $i]:
% 18.13/18.39         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 18.13/18.39           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 18.13/18.39      inference('cnf', [status(esa)], [t91_xboole_1])).
% 18.13/18.39  thf('142', plain,
% 18.13/18.39      (![X0 : $i, X1 : $i]:
% 18.13/18.39         ((k4_xboole_0 @ X0 @ X1)
% 18.13/18.39           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 18.13/18.39      inference('sup+', [status(thm)], ['10', '11'])).
% 18.13/18.39  thf('143', plain,
% 18.13/18.39      (![X24 : $i, X25 : $i]:
% 18.13/18.39         ((k3_tarski @ (k2_tarski @ X24 @ X25))
% 18.13/18.39           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 18.13/18.39      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 18.13/18.39  thf('144', plain,
% 18.13/18.39      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 18.13/18.39         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 18.13/18.39      inference('sup+', [status(thm)], ['138', '143'])).
% 18.13/18.39  thf('145', plain,
% 18.13/18.39      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) = (sk_A))),
% 18.13/18.39      inference('sup+', [status(thm)], ['76', '144'])).
% 18.13/18.39  thf('146', plain,
% 18.13/18.39      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 18.13/18.39         != (k2_subset_1 @ sk_A))),
% 18.13/18.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.13/18.39  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 18.13/18.39  thf('147', plain, (![X63 : $i]: ((k2_subset_1 @ X63) = (X63))),
% 18.13/18.39      inference('cnf', [status(esa)], [d4_subset_1])).
% 18.13/18.39  thf('148', plain,
% 18.13/18.39      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 18.13/18.39      inference('demod', [status(thm)], ['146', '147'])).
% 18.13/18.39  thf('149', plain,
% 18.13/18.39      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 18.13/18.39      inference('sup-', [status(thm)], ['14', '15'])).
% 18.13/18.39  thf('150', plain,
% 18.13/18.39      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 18.13/18.39      inference('cnf', [status(esa)], [t36_xboole_1])).
% 18.13/18.39  thf('151', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 18.13/18.39      inference('sup+', [status(thm)], ['149', '150'])).
% 18.13/18.39  thf('152', plain,
% 18.13/18.39      (![X53 : $i, X54 : $i]:
% 18.13/18.39         ((r2_hidden @ X53 @ (k1_zfmisc_1 @ X54)) | ~ (r1_tarski @ X53 @ X54))),
% 18.13/18.39      inference('simplify', [status(thm)], ['36'])).
% 18.13/18.39  thf('153', plain,
% 18.13/18.39      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 18.13/18.39      inference('sup-', [status(thm)], ['151', '152'])).
% 18.13/18.39  thf('154', plain,
% 18.13/18.39      (![X60 : $i, X61 : $i]:
% 18.13/18.39         (~ (r2_hidden @ X60 @ X61)
% 18.13/18.39          | (m1_subset_1 @ X60 @ X61)
% 18.13/18.39          | (v1_xboole_0 @ X61))),
% 18.13/18.39      inference('cnf', [status(esa)], [d2_subset_1])).
% 18.13/18.39  thf('155', plain,
% 18.13/18.39      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 18.13/18.39        | (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 18.13/18.39      inference('sup-', [status(thm)], ['153', '154'])).
% 18.13/18.39  thf('156', plain, (![X66 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X66))),
% 18.13/18.39      inference('cnf', [status(esa)], [fc1_subset_1])).
% 18.13/18.39  thf('157', plain,
% 18.13/18.39      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 18.13/18.39      inference('clc', [status(thm)], ['155', '156'])).
% 18.13/18.39  thf('158', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 18.13/18.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.13/18.39  thf(redefinition_k4_subset_1, axiom,
% 18.13/18.39    (![A:$i,B:$i,C:$i]:
% 18.13/18.39     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 18.13/18.39         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 18.13/18.39       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 18.13/18.39  thf('159', plain,
% 18.13/18.39      (![X67 : $i, X68 : $i, X69 : $i]:
% 18.13/18.39         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X68))
% 18.13/18.39          | ~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ X68))
% 18.13/18.39          | ((k4_subset_1 @ X68 @ X67 @ X69) = (k2_xboole_0 @ X67 @ X69)))),
% 18.13/18.39      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 18.13/18.39  thf('160', plain,
% 18.13/18.39      (![X58 : $i, X59 : $i]:
% 18.13/18.39         ((k3_tarski @ (k2_tarski @ X58 @ X59)) = (k2_xboole_0 @ X58 @ X59))),
% 18.13/18.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 18.13/18.39  thf('161', plain,
% 18.13/18.39      (![X67 : $i, X68 : $i, X69 : $i]:
% 18.13/18.39         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X68))
% 18.13/18.39          | ~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ X68))
% 18.13/18.39          | ((k4_subset_1 @ X68 @ X67 @ X69)
% 18.13/18.39              = (k3_tarski @ (k2_tarski @ X67 @ X69))))),
% 18.13/18.39      inference('demod', [status(thm)], ['159', '160'])).
% 18.13/18.39  thf('162', plain,
% 18.13/18.39      (![X0 : $i]:
% 18.13/18.39         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 18.13/18.39            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 18.13/18.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 18.13/18.39      inference('sup-', [status(thm)], ['158', '161'])).
% 18.13/18.39  thf('163', plain,
% 18.13/18.39      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 18.13/18.39         = (k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 18.13/18.39      inference('sup-', [status(thm)], ['157', '162'])).
% 18.13/18.39  thf('164', plain,
% 18.13/18.39      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 18.13/18.39         != (sk_A))),
% 18.13/18.39      inference('demod', [status(thm)], ['148', '163'])).
% 18.13/18.39  thf('165', plain, ($false),
% 18.13/18.39      inference('simplify_reflect-', [status(thm)], ['145', '164'])).
% 18.13/18.39  
% 18.13/18.39  % SZS output end Refutation
% 18.13/18.39  
% 18.13/18.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
