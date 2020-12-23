%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WotDy1WhxE

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:16 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 100 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  536 ( 878 expanded)
%              Number of equality atoms :   33 (  49 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t50_subset_1,conjecture,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( A != k1_xboole_0 )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ( ~ ( r2_hidden @ C @ B )
                 => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X12 ) )
      | ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_C @ ( k5_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('7',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_C @ ( k5_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k5_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ sk_C @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_C @ ( k5_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ sk_C @ ( k5_xboole_0 @ X0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_C @ ( k5_xboole_0 @ X0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ X0 )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ~ ( r2_hidden @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('39',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['41','42'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('44',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('45',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WotDy1WhxE
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.66/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.66/0.85  % Solved by: fo/fo7.sh
% 0.66/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.85  % done 521 iterations in 0.393s
% 0.66/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.66/0.85  % SZS output start Refutation
% 0.66/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.85  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.85  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.66/0.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.66/0.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.85  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.66/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.66/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.66/0.85  thf(t50_subset_1, conjecture,
% 0.66/0.85    (![A:$i]:
% 0.66/0.85     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.66/0.85       ( ![B:$i]:
% 0.66/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.85           ( ![C:$i]:
% 0.66/0.85             ( ( m1_subset_1 @ C @ A ) =>
% 0.66/0.85               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.66/0.85                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.66/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.85    (~( ![A:$i]:
% 0.66/0.85        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.66/0.85          ( ![B:$i]:
% 0.66/0.85            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.85              ( ![C:$i]:
% 0.66/0.85                ( ( m1_subset_1 @ C @ A ) =>
% 0.66/0.85                  ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.66/0.85                    ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ) )),
% 0.66/0.85    inference('cnf.neg', [status(esa)], [t50_subset_1])).
% 0.66/0.85  thf('0', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(d2_subset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( ( v1_xboole_0 @ A ) =>
% 0.66/0.85         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.66/0.85       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.66/0.85         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.66/0.85  thf('1', plain,
% 0.66/0.85      (![X22 : $i, X23 : $i]:
% 0.66/0.85         (~ (m1_subset_1 @ X22 @ X23)
% 0.66/0.85          | (r2_hidden @ X22 @ X23)
% 0.66/0.85          | (v1_xboole_0 @ X23))),
% 0.66/0.85      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.66/0.85  thf('2', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_A))),
% 0.66/0.85      inference('sup-', [status(thm)], ['0', '1'])).
% 0.66/0.85  thf(t1_xboole_0, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.66/0.85       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.66/0.85  thf('3', plain,
% 0.66/0.85      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.66/0.85         ((r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X12))
% 0.66/0.85          | (r2_hidden @ X9 @ X10)
% 0.66/0.85          | ~ (r2_hidden @ X9 @ X12))),
% 0.66/0.85      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.66/0.85  thf('4', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((v1_xboole_0 @ sk_A)
% 0.66/0.85          | (r2_hidden @ sk_C @ X0)
% 0.66/0.85          | (r2_hidden @ sk_C @ (k5_xboole_0 @ X0 @ sk_A)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['2', '3'])).
% 0.66/0.85  thf('5', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_A))),
% 0.66/0.85      inference('sup-', [status(thm)], ['0', '1'])).
% 0.66/0.85  thf(d3_xboole_0, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.66/0.85       ( ![D:$i]:
% 0.66/0.85         ( ( r2_hidden @ D @ C ) <=>
% 0.66/0.85           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.66/0.85  thf('6', plain,
% 0.66/0.85      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.66/0.85         (~ (r2_hidden @ X2 @ X5)
% 0.66/0.85          | (r2_hidden @ X2 @ X4)
% 0.66/0.85          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.66/0.85      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.66/0.85  thf('7', plain,
% 0.66/0.85      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.66/0.85         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 0.66/0.85      inference('simplify', [status(thm)], ['6'])).
% 0.66/0.85  thf('8', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['5', '7'])).
% 0.66/0.85  thf(t100_xboole_1, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.66/0.85  thf('9', plain,
% 0.66/0.85      (![X13 : $i, X14 : $i]:
% 0.66/0.85         ((k4_xboole_0 @ X13 @ X14)
% 0.66/0.85           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.66/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.85  thf(t92_xboole_1, axiom,
% 0.66/0.85    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.66/0.85  thf('10', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.66/0.85      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.66/0.85  thf(t91_xboole_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.66/0.85       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.66/0.85  thf('11', plain,
% 0.66/0.85      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.85         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.66/0.85           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.66/0.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.85  thf('12', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]:
% 0.66/0.85         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.66/0.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.66/0.85      inference('sup+', [status(thm)], ['10', '11'])).
% 0.66/0.85  thf(commutativity_k5_xboole_0, axiom,
% 0.66/0.85    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.66/0.85  thf('13', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.66/0.85      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.85  thf(t5_boole, axiom,
% 0.66/0.85    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.66/0.85  thf('14', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.66/0.85      inference('cnf', [status(esa)], [t5_boole])).
% 0.66/0.85  thf('15', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.85      inference('sup+', [status(thm)], ['13', '14'])).
% 0.66/0.85  thf('16', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]:
% 0.66/0.85         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.66/0.85      inference('demod', [status(thm)], ['12', '15'])).
% 0.66/0.85  thf('17', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]:
% 0.66/0.85         ((k3_xboole_0 @ X1 @ X0)
% 0.66/0.85           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.66/0.85      inference('sup+', [status(thm)], ['9', '16'])).
% 0.66/0.85  thf('18', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.66/0.85      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.85  thf('19', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((v1_xboole_0 @ sk_A)
% 0.66/0.85          | (r2_hidden @ sk_C @ X0)
% 0.66/0.85          | (r2_hidden @ sk_C @ (k5_xboole_0 @ X0 @ sk_A)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['2', '3'])).
% 0.66/0.85  thf('20', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((r2_hidden @ sk_C @ (k5_xboole_0 @ sk_A @ X0))
% 0.66/0.85          | (r2_hidden @ sk_C @ X0)
% 0.66/0.85          | (v1_xboole_0 @ sk_A))),
% 0.66/0.85      inference('sup+', [status(thm)], ['18', '19'])).
% 0.66/0.85  thf('21', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ X0))
% 0.66/0.85          | (v1_xboole_0 @ sk_A)
% 0.66/0.85          | (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.66/0.85      inference('sup+', [status(thm)], ['17', '20'])).
% 0.66/0.85  thf(t95_xboole_1, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( k3_xboole_0 @ A @ B ) =
% 0.66/0.85       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.66/0.85  thf('22', plain,
% 0.66/0.85      (![X20 : $i, X21 : $i]:
% 0.66/0.85         ((k3_xboole_0 @ X20 @ X21)
% 0.66/0.85           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.66/0.85              (k2_xboole_0 @ X20 @ X21)))),
% 0.66/0.85      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.66/0.85  thf('23', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.66/0.85      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.85  thf('24', plain,
% 0.66/0.85      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.85         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.66/0.85           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.66/0.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.85  thf('25', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.66/0.85           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.66/0.85      inference('sup+', [status(thm)], ['23', '24'])).
% 0.66/0.85  thf('26', plain,
% 0.66/0.85      (![X20 : $i, X21 : $i]:
% 0.66/0.85         ((k3_xboole_0 @ X20 @ X21)
% 0.66/0.85           = (k5_xboole_0 @ X21 @ 
% 0.66/0.85              (k5_xboole_0 @ X20 @ (k2_xboole_0 @ X20 @ X21))))),
% 0.66/0.85      inference('demod', [status(thm)], ['22', '25'])).
% 0.66/0.85  thf('27', plain,
% 0.66/0.85      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.85         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.66/0.85           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.66/0.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.85  thf('28', plain,
% 0.66/0.85      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.66/0.85         (~ (r2_hidden @ X9 @ X10)
% 0.66/0.85          | ~ (r2_hidden @ X9 @ X11)
% 0.66/0.85          | ~ (r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.66/0.85      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.66/0.85  thf('29', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.85         (~ (r2_hidden @ X3 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))
% 0.66/0.85          | ~ (r2_hidden @ X3 @ X0)
% 0.66/0.85          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X2 @ X1)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['27', '28'])).
% 0.66/0.85  thf('30', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.66/0.85          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X0 @ X1))
% 0.66/0.85          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['26', '29'])).
% 0.66/0.85  thf('31', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 0.66/0.85          | (v1_xboole_0 @ sk_A)
% 0.66/0.85          | ~ (r2_hidden @ sk_C @ (k2_xboole_0 @ sk_A @ X0))
% 0.66/0.85          | ~ (r2_hidden @ sk_C @ (k5_xboole_0 @ X0 @ sk_A)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['21', '30'])).
% 0.66/0.85  thf('32', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((v1_xboole_0 @ sk_A)
% 0.66/0.85          | ~ (r2_hidden @ sk_C @ (k5_xboole_0 @ X0 @ sk_A))
% 0.66/0.85          | (v1_xboole_0 @ sk_A)
% 0.66/0.85          | (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['8', '31'])).
% 0.66/0.85  thf('33', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 0.66/0.85          | ~ (r2_hidden @ sk_C @ (k5_xboole_0 @ X0 @ sk_A))
% 0.66/0.85          | (v1_xboole_0 @ sk_A))),
% 0.66/0.85      inference('simplify', [status(thm)], ['32'])).
% 0.66/0.85  thf('34', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((r2_hidden @ sk_C @ X0)
% 0.66/0.85          | (v1_xboole_0 @ sk_A)
% 0.66/0.85          | (v1_xboole_0 @ sk_A)
% 0.66/0.85          | (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['4', '33'])).
% 0.66/0.85  thf('35', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 0.66/0.85          | (v1_xboole_0 @ sk_A)
% 0.66/0.85          | (r2_hidden @ sk_C @ X0))),
% 0.66/0.85      inference('simplify', [status(thm)], ['34'])).
% 0.66/0.85  thf('36', plain, (~ (r2_hidden @ sk_C @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('37', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(d5_subset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.85       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.66/0.85  thf('38', plain,
% 0.66/0.85      (![X25 : $i, X26 : $i]:
% 0.66/0.85         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.66/0.85          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.66/0.85      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.66/0.85  thf('39', plain,
% 0.66/0.85      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.66/0.85      inference('sup-', [status(thm)], ['37', '38'])).
% 0.66/0.85  thf('40', plain, (~ (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.66/0.85      inference('demod', [status(thm)], ['36', '39'])).
% 0.66/0.85  thf('41', plain, (((r2_hidden @ sk_C @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.66/0.85      inference('sup-', [status(thm)], ['35', '40'])).
% 0.66/0.85  thf('42', plain, (~ (r2_hidden @ sk_C @ sk_B)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('43', plain, ((v1_xboole_0 @ sk_A)),
% 0.66/0.85      inference('clc', [status(thm)], ['41', '42'])).
% 0.66/0.85  thf(l13_xboole_0, axiom,
% 0.66/0.85    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.66/0.85  thf('44', plain,
% 0.66/0.85      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X8))),
% 0.66/0.85      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.66/0.85  thf('45', plain, (((sk_A) = (k1_xboole_0))),
% 0.66/0.85      inference('sup-', [status(thm)], ['43', '44'])).
% 0.66/0.85  thf('46', plain, (((sk_A) != (k1_xboole_0))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('47', plain, ($false),
% 0.66/0.85      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.66/0.85  
% 0.66/0.85  % SZS output end Refutation
% 0.66/0.85  
% 0.66/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
