%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dNgHQIqb3z

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 226 expanded)
%              Number of leaves         :   29 (  79 expanded)
%              Depth                    :   19
%              Number of atoms          :  644 (1743 expanded)
%              Number of equality atoms :   53 ( 132 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X33 @ X34 )
        = ( k4_xboole_0 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ X30 )
      | ( r2_hidden @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X35: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('14',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ( r1_tarski @ X25 @ X23 )
      | ( X24
       != ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('16',plain,(
    ! [X23: $i,X25: $i] :
      ( ( r1_tarski @ X25 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['14','16'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','19'])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('22',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('31',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('34',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','36'])).

thf('38',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,
    ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X24 )
      | ( X24
       != ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('42',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    r2_hidden @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ( m1_subset_1 @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X35: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('47',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('49',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k4_subset_1 @ X37 @ X36 @ X38 )
        = ( k2_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('53',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('54',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('57',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['51','57'])).

thf('59',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('60',plain,(
    ! [X32: $i] :
      ( ( k2_subset_1 @ X32 )
      = X32 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('61',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('63',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dNgHQIqb3z
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:01:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 210 iterations in 0.099s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.57  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.22/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(d3_tarski, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.57  thf('0', plain,
% 0.22/0.57      (![X3 : $i, X5 : $i]:
% 0.22/0.57         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.57  thf(t25_subset_1, conjecture,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.22/0.57         ( k2_subset_1 @ A ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i,B:$i]:
% 0.22/0.57        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.22/0.57            ( k2_subset_1 @ A ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.22/0.57  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(d5_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      (![X33 : $i, X34 : $i]:
% 0.22/0.57         (((k3_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))
% 0.22/0.57          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 0.22/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.57  thf(t48_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      (![X16 : $i, X17 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.22/0.57           = (k3_xboole_0 @ X16 @ X17))),
% 0.22/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.22/0.57         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.57      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.22/0.57         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.22/0.57      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.57  thf('8', plain,
% 0.22/0.57      (![X16 : $i, X17 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.22/0.57           = (k3_xboole_0 @ X16 @ X17))),
% 0.22/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.57  thf('9', plain,
% 0.22/0.57      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.22/0.57         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.57  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(d2_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.57       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.57  thf('11', plain,
% 0.22/0.57      (![X29 : $i, X30 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X29 @ X30)
% 0.22/0.57          | (r2_hidden @ X29 @ X30)
% 0.22/0.57          | (v1_xboole_0 @ X30))),
% 0.22/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.57        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.57  thf(fc1_subset_1, axiom,
% 0.22/0.57    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.57  thf('13', plain, (![X35 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 0.22/0.57      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.57  thf('14', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('clc', [status(thm)], ['12', '13'])).
% 0.22/0.57  thf(d1_zfmisc_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X25 @ X24)
% 0.22/0.57          | (r1_tarski @ X25 @ X23)
% 0.22/0.57          | ((X24) != (k1_zfmisc_1 @ X23)))),
% 0.22/0.57      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      (![X23 : $i, X25 : $i]:
% 0.22/0.57         ((r1_tarski @ X25 @ X23) | ~ (r2_hidden @ X25 @ (k1_zfmisc_1 @ X23)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.57  thf('17', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.57      inference('sup-', [status(thm)], ['14', '16'])).
% 0.22/0.57  thf(t28_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      (![X14 : $i, X15 : $i]:
% 0.22/0.57         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.22/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.57  thf('19', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.57  thf('20', plain,
% 0.22/0.57      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.22/0.57         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.57      inference('demod', [status(thm)], ['9', '19'])).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.57  thf('22', plain,
% 0.22/0.57      (((k3_subset_1 @ sk_A @ sk_B)
% 0.22/0.57         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.57      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.57  thf('23', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.57  thf(t100_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.57  thf('25', plain,
% 0.22/0.57      (![X12 : $i, X13 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X12 @ X13)
% 0.22/0.57           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.57  thf('26', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.57           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.57  thf('27', plain,
% 0.22/0.57      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.57      inference('sup+', [status(thm)], ['23', '26'])).
% 0.22/0.57  thf('28', plain,
% 0.22/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.57  thf('29', plain,
% 0.22/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.22/0.57  thf('30', plain,
% 0.22/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      (((k5_xboole_0 @ sk_A @ sk_B)
% 0.22/0.57         = (k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.57      inference('demod', [status(thm)], ['22', '29', '30'])).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.57  thf(d4_xboole_0, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.22/0.57       ( ![D:$i]:
% 0.22/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.57           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.22/0.57  thf('33', plain,
% 0.22/0.57      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X10 @ X9)
% 0.22/0.57          | (r2_hidden @ X10 @ X8)
% 0.22/0.57          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 0.22/0.57      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.22/0.57         ((r2_hidden @ X10 @ X8)
% 0.22/0.57          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['33'])).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['32', '34'])).
% 0.22/0.57  thf('36', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.22/0.57          | (r2_hidden @ X0 @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['31', '35'])).
% 0.22/0.57  thf('37', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ X0)
% 0.22/0.57          | (r2_hidden @ (sk_C @ X0 @ (k5_xboole_0 @ sk_A @ sk_B)) @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['0', '36'])).
% 0.22/0.57  thf('38', plain,
% 0.22/0.57      (![X3 : $i, X5 : $i]:
% 0.22/0.57         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.57  thf('39', plain,
% 0.22/0.57      (((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.57        | (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.57  thf('40', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.57      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.57  thf('41', plain,
% 0.22/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.57         (~ (r1_tarski @ X22 @ X23)
% 0.22/0.57          | (r2_hidden @ X22 @ X24)
% 0.22/0.57          | ((X24) != (k1_zfmisc_1 @ X23)))),
% 0.22/0.57      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.57  thf('42', plain,
% 0.22/0.57      (![X22 : $i, X23 : $i]:
% 0.22/0.57         ((r2_hidden @ X22 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X22 @ X23))),
% 0.22/0.57      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.57  thf('43', plain,
% 0.22/0.57      ((r2_hidden @ (k5_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['40', '42'])).
% 0.22/0.57  thf('44', plain,
% 0.22/0.57      (![X29 : $i, X30 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X29 @ X30)
% 0.22/0.57          | (m1_subset_1 @ X29 @ X30)
% 0.22/0.57          | (v1_xboole_0 @ X30))),
% 0.22/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.57  thf('45', plain,
% 0.22/0.57      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.57        | (m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.57  thf('46', plain, (![X35 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 0.22/0.57      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.57  thf('47', plain,
% 0.22/0.57      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('clc', [status(thm)], ['45', '46'])).
% 0.22/0.57  thf('48', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(redefinition_k4_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.22/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.57       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.22/0.57  thf('49', plain,
% 0.22/0.57      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 0.22/0.57          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37))
% 0.22/0.57          | ((k4_subset_1 @ X37 @ X36 @ X38) = (k2_xboole_0 @ X36 @ X38)))),
% 0.22/0.57      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.22/0.57  thf('50', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.22/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.57  thf('51', plain,
% 0.22/0.57      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.22/0.57         = (k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['47', '50'])).
% 0.22/0.57  thf('52', plain,
% 0.22/0.57      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.57      inference('sup+', [status(thm)], ['23', '26'])).
% 0.22/0.57  thf(t51_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.22/0.57       ( A ) ))).
% 0.22/0.57  thf('53', plain,
% 0.22/0.57      (![X18 : $i, X19 : $i]:
% 0.22/0.57         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 0.22/0.57           = (X18))),
% 0.22/0.57      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.22/0.57  thf('54', plain,
% 0.22/0.57      (((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.22/0.57         (k5_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.22/0.57      inference('sup+', [status(thm)], ['52', '53'])).
% 0.22/0.57  thf('55', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.57  thf('56', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.57  thf('57', plain,
% 0.22/0.57      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.22/0.57      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.22/0.57  thf('58', plain,
% 0.22/0.57      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.22/0.57      inference('demod', [status(thm)], ['51', '57'])).
% 0.22/0.57  thf('59', plain,
% 0.22/0.57      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.22/0.57         != (k2_subset_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.57  thf('60', plain, (![X32 : $i]: ((k2_subset_1 @ X32) = (X32))),
% 0.22/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.57  thf('61', plain,
% 0.22/0.57      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.22/0.57      inference('demod', [status(thm)], ['59', '60'])).
% 0.22/0.57  thf('62', plain,
% 0.22/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.22/0.57  thf('63', plain,
% 0.22/0.57      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.22/0.57      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.57  thf('64', plain, ($false),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['58', '63'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.22/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
