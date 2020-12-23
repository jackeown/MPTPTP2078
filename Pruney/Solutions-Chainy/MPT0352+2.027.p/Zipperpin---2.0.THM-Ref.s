%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.scRq5NBw8a

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:11 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 201 expanded)
%              Number of leaves         :   28 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  829 (1658 expanded)
%              Number of equality atoms :   49 (  83 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t31_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ C )
            <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ ( k4_xboole_0 @ X13 @ X12 ) @ ( k4_xboole_0 @ X13 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X22 )
      | ( X22
       != ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( m1_subset_1 @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('24',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

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

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('32',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( r1_tarski @ X23 @ X21 )
      | ( X22
       != ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('34',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_tarski @ X23 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ ( k4_xboole_0 @ X13 @ X12 ) @ ( k4_xboole_0 @ X13 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k3_subset_1 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['27','37'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('40',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['38','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('64',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('66',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('69',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('73',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ ( k4_xboole_0 @ X13 @ X12 ) @ ( k4_xboole_0 @ X13 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('74',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('77',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('78',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','80'])).

thf('82',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('83',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['66','85'])).

thf('87',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('88',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.scRq5NBw8a
% 0.13/0.37  % Computer   : n017.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:23:16 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.51/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.74  % Solved by: fo/fo7.sh
% 0.51/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.74  % done 1066 iterations in 0.256s
% 0.51/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.74  % SZS output start Refutation
% 0.51/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.74  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.51/0.74  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.51/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.51/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.74  thf(t31_subset_1, conjecture,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.74       ( ![C:$i]:
% 0.51/0.74         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.74           ( ( r1_tarski @ B @ C ) <=>
% 0.51/0.74             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.74    (~( ![A:$i,B:$i]:
% 0.51/0.74        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.74          ( ![C:$i]:
% 0.51/0.74            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.74              ( ( r1_tarski @ B @ C ) <=>
% 0.51/0.74                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.51/0.74    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.51/0.74  thf('0', plain,
% 0.51/0.74      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.74           (k3_subset_1 @ sk_A @ sk_B))
% 0.51/0.74        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('1', plain,
% 0.51/0.74      (~
% 0.51/0.74       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.74         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.51/0.74       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.51/0.74      inference('split', [status(esa)], ['0'])).
% 0.51/0.74  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(d5_subset_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.74       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.51/0.74  thf('3', plain,
% 0.51/0.74      (![X28 : $i, X29 : $i]:
% 0.51/0.74         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 0.51/0.74          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.51/0.74      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.51/0.74  thf('4', plain,
% 0.51/0.74      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.51/0.74      inference('sup-', [status(thm)], ['2', '3'])).
% 0.51/0.74  thf('5', plain,
% 0.51/0.74      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.74         (k3_subset_1 @ sk_A @ sk_B))
% 0.51/0.74        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('6', plain,
% 0.51/0.74      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.51/0.74      inference('split', [status(esa)], ['5'])).
% 0.51/0.74  thf(t34_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( r1_tarski @ A @ B ) =>
% 0.51/0.74       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.51/0.74  thf('7', plain,
% 0.51/0.74      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.51/0.74         (~ (r1_tarski @ X11 @ X12)
% 0.51/0.74          | (r1_tarski @ (k4_xboole_0 @ X13 @ X12) @ (k4_xboole_0 @ X13 @ X11)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.51/0.74  thf('8', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B)))
% 0.51/0.74         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['6', '7'])).
% 0.51/0.74  thf('9', plain,
% 0.51/0.74      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.74         (k4_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['4', '8'])).
% 0.51/0.74  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('11', plain,
% 0.51/0.74      (![X28 : $i, X29 : $i]:
% 0.51/0.74         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 0.51/0.74          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.51/0.74      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.51/0.74  thf('12', plain,
% 0.51/0.74      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.51/0.74      inference('sup-', [status(thm)], ['10', '11'])).
% 0.51/0.74  thf('13', plain,
% 0.51/0.74      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.74         (k3_subset_1 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.51/0.74      inference('demod', [status(thm)], ['9', '12'])).
% 0.51/0.74  thf('14', plain,
% 0.51/0.74      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.74           (k3_subset_1 @ sk_A @ sk_B)))
% 0.51/0.74         <= (~
% 0.51/0.74             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.74               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.51/0.74      inference('split', [status(esa)], ['0'])).
% 0.51/0.74  thf('15', plain,
% 0.51/0.74      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.74         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.51/0.74       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.51/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.51/0.74  thf('16', plain,
% 0.51/0.74      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.74         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.51/0.74       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.51/0.74      inference('split', [status(esa)], ['5'])).
% 0.51/0.74  thf(d10_xboole_0, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.51/0.74  thf('17', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.51/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.74  thf('18', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.51/0.74      inference('simplify', [status(thm)], ['17'])).
% 0.51/0.74  thf(d1_zfmisc_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.51/0.74       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.51/0.74  thf('19', plain,
% 0.51/0.74      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.51/0.74         (~ (r1_tarski @ X20 @ X21)
% 0.51/0.74          | (r2_hidden @ X20 @ X22)
% 0.51/0.74          | ((X22) != (k1_zfmisc_1 @ X21)))),
% 0.51/0.74      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.51/0.74  thf('20', plain,
% 0.51/0.74      (![X20 : $i, X21 : $i]:
% 0.51/0.74         ((r2_hidden @ X20 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X20 @ X21))),
% 0.51/0.74      inference('simplify', [status(thm)], ['19'])).
% 0.51/0.74  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['18', '20'])).
% 0.51/0.74  thf(d2_subset_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( ( v1_xboole_0 @ A ) =>
% 0.51/0.74         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.51/0.74       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.51/0.74         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.51/0.74  thf('22', plain,
% 0.51/0.74      (![X25 : $i, X26 : $i]:
% 0.51/0.74         (~ (r2_hidden @ X25 @ X26)
% 0.51/0.74          | (m1_subset_1 @ X25 @ X26)
% 0.51/0.74          | (v1_xboole_0 @ X26))),
% 0.51/0.74      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.51/0.74  thf('23', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.51/0.74          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['21', '22'])).
% 0.51/0.74  thf(fc1_subset_1, axiom,
% 0.51/0.74    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.51/0.74  thf('24', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.51/0.74      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.51/0.74  thf('25', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.51/0.74      inference('clc', [status(thm)], ['23', '24'])).
% 0.51/0.74  thf('26', plain,
% 0.51/0.74      (![X28 : $i, X29 : $i]:
% 0.51/0.74         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 0.51/0.74          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.51/0.74      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.51/0.74  thf('27', plain,
% 0.51/0.74      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['25', '26'])).
% 0.51/0.74  thf('28', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('29', plain,
% 0.51/0.74      (![X25 : $i, X26 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X25 @ X26)
% 0.51/0.74          | (r2_hidden @ X25 @ X26)
% 0.51/0.74          | (v1_xboole_0 @ X26))),
% 0.51/0.74      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.51/0.74  thf('30', plain,
% 0.51/0.74      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.51/0.74        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.74  thf('31', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.51/0.74      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.51/0.74  thf('32', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.51/0.74      inference('clc', [status(thm)], ['30', '31'])).
% 0.51/0.74  thf('33', plain,
% 0.51/0.74      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.51/0.74         (~ (r2_hidden @ X23 @ X22)
% 0.51/0.74          | (r1_tarski @ X23 @ X21)
% 0.51/0.74          | ((X22) != (k1_zfmisc_1 @ X21)))),
% 0.51/0.74      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.51/0.74  thf('34', plain,
% 0.51/0.74      (![X21 : $i, X23 : $i]:
% 0.51/0.74         ((r1_tarski @ X23 @ X21) | ~ (r2_hidden @ X23 @ (k1_zfmisc_1 @ X21)))),
% 0.51/0.74      inference('simplify', [status(thm)], ['33'])).
% 0.51/0.74  thf('35', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.51/0.74      inference('sup-', [status(thm)], ['32', '34'])).
% 0.51/0.74  thf('36', plain,
% 0.51/0.74      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.51/0.74         (~ (r1_tarski @ X11 @ X12)
% 0.51/0.74          | (r1_tarski @ (k4_xboole_0 @ X13 @ X12) @ (k4_xboole_0 @ X13 @ X11)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.51/0.74  thf('37', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.51/0.74      inference('sup-', [status(thm)], ['35', '36'])).
% 0.51/0.74  thf('38', plain,
% 0.51/0.74      ((r1_tarski @ (k4_xboole_0 @ sk_B @ sk_A) @ (k3_subset_1 @ sk_B @ sk_B))),
% 0.51/0.74      inference('sup+', [status(thm)], ['27', '37'])).
% 0.51/0.74  thf(t39_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.51/0.74  thf('39', plain,
% 0.51/0.74      (![X16 : $i, X17 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 0.51/0.74           = (k2_xboole_0 @ X16 @ X17))),
% 0.51/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.51/0.74  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.51/0.74  thf('40', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.51/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.51/0.74  thf(t12_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.51/0.74  thf('41', plain,
% 0.51/0.74      (![X8 : $i, X9 : $i]:
% 0.51/0.74         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.51/0.74      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.51/0.74  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['40', '41'])).
% 0.51/0.74  thf('43', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['39', '42'])).
% 0.51/0.74  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['40', '41'])).
% 0.51/0.74  thf('45', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['43', '44'])).
% 0.51/0.74  thf(t48_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.51/0.74  thf('46', plain,
% 0.51/0.74      (![X18 : $i, X19 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.51/0.74           = (k3_xboole_0 @ X18 @ X19))),
% 0.51/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.51/0.74  thf('47', plain,
% 0.51/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['45', '46'])).
% 0.51/0.74  thf(commutativity_k3_xboole_0, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.51/0.74  thf('48', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.74  thf('49', plain,
% 0.51/0.74      (![X18 : $i, X19 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.51/0.74           = (k3_xboole_0 @ X18 @ X19))),
% 0.51/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.51/0.74  thf(t36_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.51/0.74  thf('50', plain,
% 0.51/0.74      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.51/0.74      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.51/0.74  thf('51', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.51/0.74      inference('sup+', [status(thm)], ['49', '50'])).
% 0.51/0.74  thf('52', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.51/0.74      inference('sup+', [status(thm)], ['48', '51'])).
% 0.51/0.74  thf('53', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.51/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.51/0.74  thf('54', plain,
% 0.51/0.74      (![X2 : $i, X4 : $i]:
% 0.51/0.74         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.51/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.74  thf('55', plain,
% 0.51/0.74      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.51/0.74  thf('56', plain,
% 0.51/0.74      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['52', '55'])).
% 0.51/0.74  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['47', '56'])).
% 0.51/0.74  thf('58', plain,
% 0.51/0.74      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['25', '26'])).
% 0.51/0.74  thf('59', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['57', '58'])).
% 0.51/0.74  thf('60', plain, ((r1_tarski @ (k4_xboole_0 @ sk_B @ sk_A) @ k1_xboole_0)),
% 0.51/0.74      inference('demod', [status(thm)], ['38', '59'])).
% 0.51/0.74  thf('61', plain,
% 0.51/0.74      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.51/0.74  thf('62', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['60', '61'])).
% 0.51/0.74  thf('63', plain,
% 0.51/0.74      (![X18 : $i, X19 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.51/0.74           = (k3_xboole_0 @ X18 @ X19))),
% 0.51/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.51/0.74  thf('64', plain,
% 0.51/0.74      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.51/0.74      inference('sup+', [status(thm)], ['62', '63'])).
% 0.51/0.74  thf('65', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['43', '44'])).
% 0.51/0.74  thf('66', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.51/0.74      inference('demod', [status(thm)], ['64', '65'])).
% 0.51/0.74  thf('67', plain,
% 0.51/0.74      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.51/0.74      inference('sup-', [status(thm)], ['10', '11'])).
% 0.51/0.74  thf('68', plain,
% 0.51/0.74      (![X18 : $i, X19 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.51/0.74           = (k3_xboole_0 @ X18 @ X19))),
% 0.51/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.51/0.74  thf('69', plain,
% 0.51/0.75      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.51/0.75         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.51/0.75      inference('sup+', [status(thm)], ['67', '68'])).
% 0.51/0.75  thf('70', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.75  thf('71', plain,
% 0.51/0.75      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.51/0.75         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.51/0.75      inference('demod', [status(thm)], ['69', '70'])).
% 0.51/0.75  thf('72', plain,
% 0.51/0.75      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.75         (k3_subset_1 @ sk_A @ sk_B)))
% 0.51/0.75         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.75               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.51/0.75      inference('split', [status(esa)], ['5'])).
% 0.51/0.75  thf('73', plain,
% 0.51/0.75      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.51/0.75         (~ (r1_tarski @ X11 @ X12)
% 0.51/0.75          | (r1_tarski @ (k4_xboole_0 @ X13 @ X12) @ (k4_xboole_0 @ X13 @ X11)))),
% 0.51/0.75      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.51/0.75  thf('74', plain,
% 0.51/0.75      ((![X0 : $i]:
% 0.51/0.75          (r1_tarski @ (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 0.51/0.75           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))))
% 0.51/0.75         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.75               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.51/0.75      inference('sup-', [status(thm)], ['72', '73'])).
% 0.51/0.75  thf('75', plain,
% 0.51/0.75      (((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 0.51/0.75         (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1))))
% 0.51/0.75         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.75               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.51/0.75      inference('sup+', [status(thm)], ['71', '74'])).
% 0.51/0.75  thf('76', plain,
% 0.51/0.75      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.51/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.51/0.75  thf('77', plain,
% 0.51/0.75      (![X18 : $i, X19 : $i]:
% 0.51/0.75         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.51/0.75           = (k3_xboole_0 @ X18 @ X19))),
% 0.51/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.51/0.75  thf('78', plain,
% 0.51/0.75      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.51/0.75         = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.51/0.75      inference('sup+', [status(thm)], ['76', '77'])).
% 0.51/0.75  thf('79', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.75  thf('80', plain,
% 0.51/0.75      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.51/0.75         = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.51/0.75      inference('demod', [status(thm)], ['78', '79'])).
% 0.51/0.75  thf('81', plain,
% 0.51/0.75      (((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 0.51/0.75         (k3_xboole_0 @ sk_C_1 @ sk_A)))
% 0.51/0.75         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.75               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.51/0.75      inference('demod', [status(thm)], ['75', '80'])).
% 0.51/0.75  thf('82', plain,
% 0.51/0.75      (![X18 : $i, X19 : $i]:
% 0.51/0.75         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.51/0.75           = (k3_xboole_0 @ X18 @ X19))),
% 0.51/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.51/0.75  thf(t106_xboole_1, axiom,
% 0.51/0.75    (![A:$i,B:$i,C:$i]:
% 0.51/0.75     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.51/0.75       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.51/0.75  thf('83', plain,
% 0.51/0.75      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.51/0.75         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.51/0.75      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.51/0.75  thf('84', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.75         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 0.51/0.75      inference('sup-', [status(thm)], ['82', '83'])).
% 0.51/0.75  thf('85', plain,
% 0.51/0.75      (((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C_1))
% 0.51/0.75         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.75               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.51/0.75      inference('sup-', [status(thm)], ['81', '84'])).
% 0.51/0.75  thf('86', plain,
% 0.51/0.75      (((r1_tarski @ sk_B @ sk_C_1))
% 0.51/0.75         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.75               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.51/0.75      inference('sup+', [status(thm)], ['66', '85'])).
% 0.51/0.75  thf('87', plain,
% 0.51/0.75      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.51/0.75      inference('split', [status(esa)], ['0'])).
% 0.51/0.75  thf('88', plain,
% 0.51/0.75      (~
% 0.51/0.75       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.51/0.75         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.51/0.75       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.51/0.75      inference('sup-', [status(thm)], ['86', '87'])).
% 0.51/0.75  thf('89', plain, ($false),
% 0.51/0.75      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '88'])).
% 0.51/0.75  
% 0.51/0.75  % SZS output end Refutation
% 0.51/0.75  
% 0.51/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
