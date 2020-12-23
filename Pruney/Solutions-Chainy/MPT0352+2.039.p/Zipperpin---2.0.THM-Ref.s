%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UF6IgNRQBk

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:13 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 193 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :   24
%              Number of atoms          :  800 (1631 expanded)
%              Number of equality atoms :   35 (  68 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
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

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X19 @ ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['17','41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('44',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('45',plain,
    ( ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X19 @ ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
        | ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('52',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('54',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X19 @ ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('58',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
      = sk_A )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('60',plain,
    ( ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A )
      | ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
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

thf('62',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ X30 )
      | ( r2_hidden @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('64',plain,(
    ! [X34: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('65',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['63','64'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('66',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( r1_tarski @ X27 @ X25 )
      | ( X26
       != ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('67',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_tarski @ X27 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('70',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','72'])).

thf('74',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('75',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_B @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UF6IgNRQBk
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:41:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.74/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/1.00  % Solved by: fo/fo7.sh
% 0.74/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/1.00  % done 1692 iterations in 0.550s
% 0.74/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/1.00  % SZS output start Refutation
% 0.74/1.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.74/1.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/1.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/1.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.74/1.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/1.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.74/1.00  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.74/1.00  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.74/1.00  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.74/1.00  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.74/1.00  thf(t31_subset_1, conjecture,
% 0.74/1.00    (![A:$i,B:$i]:
% 0.74/1.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/1.00       ( ![C:$i]:
% 0.74/1.00         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/1.00           ( ( r1_tarski @ B @ C ) <=>
% 0.74/1.00             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.74/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.74/1.00    (~( ![A:$i,B:$i]:
% 0.74/1.00        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/1.00          ( ![C:$i]:
% 0.74/1.00            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/1.00              ( ( r1_tarski @ B @ C ) <=>
% 0.74/1.00                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.74/1.00    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.74/1.00  thf('0', plain,
% 0.74/1.00      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00           (k3_subset_1 @ sk_A @ sk_B))
% 0.74/1.00        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 0.74/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.00  thf('1', plain,
% 0.74/1.00      (~
% 0.74/1.00       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.74/1.00       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.74/1.00      inference('split', [status(esa)], ['0'])).
% 0.74/1.00  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.74/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.00  thf(d5_subset_1, axiom,
% 0.74/1.00    (![A:$i,B:$i]:
% 0.74/1.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/1.00       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.74/1.00  thf('3', plain,
% 0.74/1.00      (![X32 : $i, X33 : $i]:
% 0.74/1.00         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 0.74/1.00          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.74/1.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.74/1.00  thf('4', plain,
% 0.74/1.00      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.74/1.00      inference('sup-', [status(thm)], ['2', '3'])).
% 0.74/1.00  thf('5', plain,
% 0.74/1.00      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00         (k3_subset_1 @ sk_A @ sk_B))
% 0.74/1.00        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.74/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.00  thf('6', plain,
% 0.74/1.00      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.74/1.00      inference('split', [status(esa)], ['5'])).
% 0.74/1.00  thf(t34_xboole_1, axiom,
% 0.74/1.00    (![A:$i,B:$i,C:$i]:
% 0.74/1.00     ( ( r1_tarski @ A @ B ) =>
% 0.74/1.00       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.74/1.00  thf('7', plain,
% 0.74/1.00      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.74/1.00         (~ (r1_tarski @ X11 @ X12)
% 0.74/1.00          | (r1_tarski @ (k4_xboole_0 @ X13 @ X12) @ (k4_xboole_0 @ X13 @ X11)))),
% 0.74/1.00      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.74/1.00  thf('8', plain,
% 0.74/1.00      ((![X0 : $i]:
% 0.74/1.00          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B)))
% 0.74/1.00         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['6', '7'])).
% 0.74/1.00  thf('9', plain,
% 0.74/1.00      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00         (k4_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.74/1.00      inference('sup+', [status(thm)], ['4', '8'])).
% 0.74/1.00  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.74/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.00  thf('11', plain,
% 0.74/1.00      (![X32 : $i, X33 : $i]:
% 0.74/1.00         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 0.74/1.00          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.74/1.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.74/1.00  thf('12', plain,
% 0.74/1.00      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.74/1.00      inference('sup-', [status(thm)], ['10', '11'])).
% 0.74/1.00  thf('13', plain,
% 0.74/1.00      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00         (k3_subset_1 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.74/1.00      inference('demod', [status(thm)], ['9', '12'])).
% 0.74/1.00  thf('14', plain,
% 0.74/1.00      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00           (k3_subset_1 @ sk_A @ sk_B)))
% 0.74/1.00         <= (~
% 0.74/1.00             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.74/1.00      inference('split', [status(esa)], ['0'])).
% 0.74/1.00  thf('15', plain,
% 0.74/1.00      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.74/1.00       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.74/1.00      inference('sup-', [status(thm)], ['13', '14'])).
% 0.74/1.00  thf('16', plain,
% 0.74/1.00      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.74/1.00       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.74/1.00      inference('split', [status(esa)], ['5'])).
% 0.74/1.00  thf('17', plain,
% 0.74/1.00      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.74/1.00      inference('sup-', [status(thm)], ['10', '11'])).
% 0.74/1.00  thf(t36_xboole_1, axiom,
% 0.74/1.00    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.74/1.00  thf('18', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.74/1.00      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.74/1.00  thf('19', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.74/1.00      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.74/1.00  thf(l32_xboole_1, axiom,
% 0.74/1.00    (![A:$i,B:$i]:
% 0.74/1.00     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.74/1.00  thf('20', plain,
% 0.74/1.00      (![X2 : $i, X4 : $i]:
% 0.74/1.00         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.74/1.00      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.74/1.00  thf('21', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.74/1.00      inference('sup-', [status(thm)], ['19', '20'])).
% 0.74/1.00  thf(t38_xboole_1, axiom,
% 0.74/1.00    (![A:$i,B:$i]:
% 0.74/1.00     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.74/1.00       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.74/1.00  thf('22', plain,
% 0.74/1.00      (![X16 : $i, X17 : $i]:
% 0.74/1.00         (((X16) = (k1_xboole_0))
% 0.74/1.00          | ~ (r1_tarski @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.74/1.00      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.74/1.00  thf('23', plain,
% 0.74/1.00      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['21', '22'])).
% 0.74/1.00  thf('24', plain,
% 0.74/1.00      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.74/1.00      inference('sup-', [status(thm)], ['18', '23'])).
% 0.74/1.00  thf('25', plain,
% 0.74/1.00      (![X2 : $i, X3 : $i]:
% 0.74/1.00         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.74/1.00      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.74/1.00  thf('26', plain,
% 0.74/1.00      (![X0 : $i]:
% 0.74/1.00         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.74/1.00      inference('sup-', [status(thm)], ['24', '25'])).
% 0.74/1.00  thf('27', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.74/1.00      inference('simplify', [status(thm)], ['26'])).
% 0.74/1.00  thf(t106_xboole_1, axiom,
% 0.74/1.00    (![A:$i,B:$i,C:$i]:
% 0.74/1.00     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.74/1.00       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.74/1.00  thf('28', plain,
% 0.74/1.00      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.74/1.00         ((r1_xboole_0 @ X5 @ X7)
% 0.74/1.00          | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.74/1.00      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.74/1.00  thf('29', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.74/1.00      inference('sup-', [status(thm)], ['27', '28'])).
% 0.74/1.00  thf(symmetry_r1_xboole_0, axiom,
% 0.74/1.00    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.74/1.00  thf('30', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.74/1.00      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.74/1.00  thf('31', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.74/1.00      inference('sup-', [status(thm)], ['29', '30'])).
% 0.74/1.00  thf(t83_xboole_1, axiom,
% 0.74/1.00    (![A:$i,B:$i]:
% 0.74/1.00     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.74/1.00  thf('32', plain,
% 0.74/1.00      (![X21 : $i, X22 : $i]:
% 0.74/1.00         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 0.74/1.00      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.74/1.00  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.74/1.00      inference('sup-', [status(thm)], ['31', '32'])).
% 0.74/1.00  thf('34', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.74/1.00      inference('sup-', [status(thm)], ['19', '20'])).
% 0.74/1.00  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.74/1.00      inference('sup+', [status(thm)], ['33', '34'])).
% 0.74/1.00  thf(t81_xboole_1, axiom,
% 0.74/1.00    (![A:$i,B:$i,C:$i]:
% 0.74/1.00     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.74/1.00       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.74/1.00  thf('36', plain,
% 0.74/1.00      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.74/1.00         ((r1_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.74/1.00          | ~ (r1_xboole_0 @ X19 @ (k4_xboole_0 @ X18 @ X20)))),
% 0.74/1.00      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.74/1.00  thf('37', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         (~ (r1_xboole_0 @ X1 @ k1_xboole_0)
% 0.74/1.00          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['35', '36'])).
% 0.74/1.00  thf('38', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.74/1.00      inference('sup-', [status(thm)], ['29', '30'])).
% 0.74/1.00  thf('39', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.74/1.00      inference('demod', [status(thm)], ['37', '38'])).
% 0.74/1.00  thf('40', plain,
% 0.74/1.00      (![X21 : $i, X22 : $i]:
% 0.74/1.00         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 0.74/1.00      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.74/1.00  thf('41', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.74/1.00      inference('sup-', [status(thm)], ['39', '40'])).
% 0.74/1.00  thf('42', plain,
% 0.74/1.00      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.74/1.00      inference('sup+', [status(thm)], ['17', '41'])).
% 0.74/1.00  thf('43', plain,
% 0.74/1.00      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00         (k3_subset_1 @ sk_A @ sk_B)))
% 0.74/1.00         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.74/1.00      inference('split', [status(esa)], ['5'])).
% 0.74/1.00  thf('44', plain,
% 0.74/1.00      (![X2 : $i, X4 : $i]:
% 0.74/1.00         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.74/1.00      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.74/1.00  thf('45', plain,
% 0.74/1.00      ((((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00          (k3_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0)))
% 0.74/1.00         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.74/1.00      inference('sup-', [status(thm)], ['43', '44'])).
% 0.74/1.00  thf('46', plain,
% 0.74/1.00      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.74/1.00         ((r1_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.74/1.00          | ~ (r1_xboole_0 @ X19 @ (k4_xboole_0 @ X18 @ X20)))),
% 0.74/1.00      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.74/1.00  thf('47', plain,
% 0.74/1.00      ((![X0 : $i]:
% 0.74/1.00          (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.74/1.00           | (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00              (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)))))
% 0.74/1.00         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.74/1.00      inference('sup-', [status(thm)], ['45', '46'])).
% 0.74/1.00  thf('48', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.74/1.00      inference('sup-', [status(thm)], ['29', '30'])).
% 0.74/1.00  thf('49', plain,
% 0.74/1.00      ((![X0 : $i]:
% 0.74/1.00          (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.74/1.00         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.74/1.00      inference('demod', [status(thm)], ['47', '48'])).
% 0.74/1.00  thf('50', plain,
% 0.74/1.00      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))
% 0.74/1.00         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.74/1.00      inference('sup+', [status(thm)], ['42', '49'])).
% 0.74/1.00  thf('51', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.74/1.00      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.74/1.00  thf('52', plain,
% 0.74/1.00      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.74/1.00         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.74/1.00      inference('sup-', [status(thm)], ['50', '51'])).
% 0.74/1.00  thf('53', plain,
% 0.74/1.00      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.74/1.00      inference('sup-', [status(thm)], ['2', '3'])).
% 0.74/1.00  thf('54', plain,
% 0.74/1.00      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.74/1.00         ((r1_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.74/1.00          | ~ (r1_xboole_0 @ X19 @ (k4_xboole_0 @ X18 @ X20)))),
% 0.74/1.00      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.74/1.00  thf('55', plain,
% 0.74/1.00      (![X0 : $i]:
% 0.74/1.00         (~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.74/1.00          | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['53', '54'])).
% 0.74/1.00  thf('56', plain,
% 0.74/1.00      (((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)))
% 0.74/1.00         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.74/1.00      inference('sup-', [status(thm)], ['52', '55'])).
% 0.74/1.00  thf('57', plain,
% 0.74/1.00      (![X21 : $i, X22 : $i]:
% 0.74/1.00         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 0.74/1.00      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.74/1.00  thf('58', plain,
% 0.74/1.00      ((((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)) = (sk_A)))
% 0.74/1.00         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.74/1.00      inference('sup-', [status(thm)], ['56', '57'])).
% 0.74/1.00  thf('59', plain,
% 0.74/1.00      (![X16 : $i, X17 : $i]:
% 0.74/1.00         (((X16) = (k1_xboole_0))
% 0.74/1.00          | ~ (r1_tarski @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.74/1.00      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.74/1.00  thf('60', plain,
% 0.74/1.00      (((~ (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_C_1) @ sk_A)
% 0.74/1.00         | ((k4_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))))
% 0.74/1.00         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.74/1.00      inference('sup-', [status(thm)], ['58', '59'])).
% 0.74/1.00  thf('61', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.74/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.00  thf(d2_subset_1, axiom,
% 0.74/1.00    (![A:$i,B:$i]:
% 0.74/1.00     ( ( ( v1_xboole_0 @ A ) =>
% 0.74/1.00         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.74/1.00       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.74/1.00         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.74/1.00  thf('62', plain,
% 0.74/1.00      (![X29 : $i, X30 : $i]:
% 0.74/1.00         (~ (m1_subset_1 @ X29 @ X30)
% 0.74/1.00          | (r2_hidden @ X29 @ X30)
% 0.74/1.00          | (v1_xboole_0 @ X30))),
% 0.74/1.00      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.74/1.00  thf('63', plain,
% 0.74/1.00      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.74/1.00        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['61', '62'])).
% 0.74/1.00  thf(fc1_subset_1, axiom,
% 0.74/1.00    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.74/1.00  thf('64', plain, (![X34 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X34))),
% 0.74/1.00      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.74/1.00  thf('65', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.74/1.00      inference('clc', [status(thm)], ['63', '64'])).
% 0.74/1.00  thf(d1_zfmisc_1, axiom,
% 0.74/1.00    (![A:$i,B:$i]:
% 0.74/1.00     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.74/1.00       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.74/1.00  thf('66', plain,
% 0.74/1.00      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.74/1.00         (~ (r2_hidden @ X27 @ X26)
% 0.74/1.00          | (r1_tarski @ X27 @ X25)
% 0.74/1.00          | ((X26) != (k1_zfmisc_1 @ X25)))),
% 0.74/1.00      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.74/1.00  thf('67', plain,
% 0.74/1.00      (![X25 : $i, X27 : $i]:
% 0.74/1.00         ((r1_tarski @ X27 @ X25) | ~ (r2_hidden @ X27 @ (k1_zfmisc_1 @ X25)))),
% 0.74/1.00      inference('simplify', [status(thm)], ['66'])).
% 0.74/1.00  thf('68', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.74/1.00      inference('sup-', [status(thm)], ['65', '67'])).
% 0.74/1.00  thf('69', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.74/1.00      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.74/1.00  thf(t1_xboole_1, axiom,
% 0.74/1.00    (![A:$i,B:$i,C:$i]:
% 0.74/1.00     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.74/1.00       ( r1_tarski @ A @ C ) ))).
% 0.74/1.00  thf('70', plain,
% 0.74/1.00      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.74/1.00         (~ (r1_tarski @ X8 @ X9)
% 0.74/1.00          | ~ (r1_tarski @ X9 @ X10)
% 0.74/1.00          | (r1_tarski @ X8 @ X10))),
% 0.74/1.00      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.74/1.00  thf('71', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.74/1.00      inference('sup-', [status(thm)], ['69', '70'])).
% 0.74/1.00  thf('72', plain,
% 0.74/1.00      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.74/1.00      inference('sup-', [status(thm)], ['68', '71'])).
% 0.74/1.00  thf('73', plain,
% 0.74/1.00      ((((k4_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0)))
% 0.74/1.00         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.74/1.00      inference('demod', [status(thm)], ['60', '72'])).
% 0.74/1.00  thf('74', plain,
% 0.74/1.00      (![X2 : $i, X3 : $i]:
% 0.74/1.00         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.74/1.00      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.74/1.00  thf('75', plain,
% 0.74/1.00      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_B @ sk_C_1)))
% 0.74/1.00         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.74/1.00      inference('sup-', [status(thm)], ['73', '74'])).
% 0.74/1.00  thf('76', plain,
% 0.74/1.00      (((r1_tarski @ sk_B @ sk_C_1))
% 0.74/1.00         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.74/1.00      inference('simplify', [status(thm)], ['75'])).
% 0.74/1.00  thf('77', plain,
% 0.74/1.00      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.74/1.00      inference('split', [status(esa)], ['0'])).
% 0.74/1.00  thf('78', plain,
% 0.74/1.00      (~
% 0.74/1.00       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.74/1.00         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.74/1.00       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.74/1.00      inference('sup-', [status(thm)], ['76', '77'])).
% 0.74/1.00  thf('79', plain, ($false),
% 0.74/1.00      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '78'])).
% 0.74/1.00  
% 0.74/1.00  % SZS output end Refutation
% 0.74/1.00  
% 0.74/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
