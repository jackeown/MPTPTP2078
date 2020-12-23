%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SG5f4eAnCl

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:07 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 356 expanded)
%              Number of leaves         :   33 ( 120 expanded)
%              Depth                    :   21
%              Number of atoms          :  890 (3003 expanded)
%              Number of equality atoms :   43 ( 150 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k3_subset_1 @ X48 @ X49 )
        = ( k4_xboole_0 @ X48 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('7',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k3_subset_1 @ X48 @ X49 )
        = ( k4_xboole_0 @ X48 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('15',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ X46 )
      | ( r2_hidden @ X45 @ X46 )
      | ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X50: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('22',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X41 @ X40 )
      | ( r1_tarski @ X41 @ X39 )
      | ( X40
       != ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('24',plain,(
    ! [X39: $i,X41: $i] :
      ( ( r1_tarski @ X41 @ X39 )
      | ~ ( r2_hidden @ X41 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['22','24'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('30',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_tarski @ X19 @ X20 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('38',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_tarski @ X35 @ X34 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('47',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['37','42','45','46'])).

thf('48',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['17','47'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('49',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( r1_tarski @ sk_B @ sk_C_1 )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ X46 )
      | ( r2_hidden @ X45 @ X46 )
      | ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X50: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('56',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X39: $i,X41: $i] :
      ( ( r1_tarski @ X41 @ X39 )
      | ~ ( r2_hidden @ X41 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('58',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','61'])).

thf('63',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','62'])).

thf('64',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('65',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('66',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('71',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('75',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('79',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['66','79'])).

thf('81',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('82',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ( r1_xboole_0 @ X26 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('83',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('85',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('87',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','61','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['85','87'])).

thf('89',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('91',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_C_1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['80','94'])).

thf('96',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('97',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['63','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SG5f4eAnCl
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:10:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 1.64/1.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.64/1.84  % Solved by: fo/fo7.sh
% 1.64/1.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.64/1.84  % done 2682 iterations in 1.393s
% 1.64/1.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.64/1.84  % SZS output start Refutation
% 1.64/1.84  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.64/1.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.64/1.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.64/1.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.64/1.84  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.64/1.84  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.64/1.84  thf(sk_B_type, type, sk_B: $i).
% 1.64/1.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.64/1.84  thf(sk_A_type, type, sk_A: $i).
% 1.64/1.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.64/1.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.64/1.84  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.64/1.84  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.64/1.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.64/1.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.64/1.84  thf(t31_subset_1, conjecture,
% 1.64/1.84    (![A:$i,B:$i]:
% 1.64/1.84     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.64/1.84       ( ![C:$i]:
% 1.64/1.84         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.64/1.84           ( ( r1_tarski @ B @ C ) <=>
% 1.64/1.84             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.64/1.84  thf(zf_stmt_0, negated_conjecture,
% 1.64/1.84    (~( ![A:$i,B:$i]:
% 1.64/1.84        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.64/1.84          ( ![C:$i]:
% 1.64/1.84            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.64/1.84              ( ( r1_tarski @ B @ C ) <=>
% 1.64/1.84                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 1.64/1.84    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 1.64/1.84  thf('0', plain,
% 1.64/1.84      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.64/1.84           (k3_subset_1 @ sk_A @ sk_B))
% 1.64/1.84        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 1.64/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.84  thf('1', plain,
% 1.64/1.84      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.64/1.84           (k3_subset_1 @ sk_A @ sk_B)))
% 1.64/1.84         <= (~
% 1.64/1.84             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.64/1.84               (k3_subset_1 @ sk_A @ sk_B))))),
% 1.64/1.84      inference('split', [status(esa)], ['0'])).
% 1.64/1.84  thf('2', plain,
% 1.64/1.84      (~
% 1.64/1.84       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.64/1.84         (k3_subset_1 @ sk_A @ sk_B))) | 
% 1.64/1.84       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 1.64/1.84      inference('split', [status(esa)], ['0'])).
% 1.64/1.84  thf('3', plain,
% 1.64/1.84      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.64/1.84         (k3_subset_1 @ sk_A @ sk_B))
% 1.64/1.84        | (r1_tarski @ sk_B @ sk_C_1))),
% 1.64/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.84  thf('4', plain,
% 1.64/1.84      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.64/1.84         (k3_subset_1 @ sk_A @ sk_B)))
% 1.64/1.84         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.64/1.84               (k3_subset_1 @ sk_A @ sk_B))))),
% 1.64/1.84      inference('split', [status(esa)], ['3'])).
% 1.64/1.84  thf('5', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.64/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.84  thf(d5_subset_1, axiom,
% 1.64/1.84    (![A:$i,B:$i]:
% 1.64/1.84     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.64/1.84       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.64/1.84  thf('6', plain,
% 1.64/1.84      (![X48 : $i, X49 : $i]:
% 1.64/1.84         (((k3_subset_1 @ X48 @ X49) = (k4_xboole_0 @ X48 @ X49))
% 1.64/1.84          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X48)))),
% 1.64/1.84      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.64/1.84  thf('7', plain,
% 1.64/1.84      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.64/1.84      inference('sup-', [status(thm)], ['5', '6'])).
% 1.64/1.84  thf(t106_xboole_1, axiom,
% 1.64/1.84    (![A:$i,B:$i,C:$i]:
% 1.64/1.84     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.64/1.84       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.64/1.84  thf('8', plain,
% 1.64/1.84      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.64/1.84         ((r1_xboole_0 @ X7 @ X9)
% 1.64/1.84          | ~ (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X9)))),
% 1.64/1.84      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.64/1.84  thf('9', plain,
% 1.64/1.84      (![X0 : $i]:
% 1.64/1.84         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 1.64/1.84          | (r1_xboole_0 @ X0 @ sk_B))),
% 1.64/1.84      inference('sup-', [status(thm)], ['7', '8'])).
% 1.64/1.84  thf('10', plain,
% 1.64/1.84      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))
% 1.64/1.84         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.64/1.84               (k3_subset_1 @ sk_A @ sk_B))))),
% 1.64/1.84      inference('sup-', [status(thm)], ['4', '9'])).
% 1.64/1.84  thf(symmetry_r1_xboole_0, axiom,
% 1.64/1.84    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.64/1.84  thf('11', plain,
% 1.64/1.84      (![X3 : $i, X4 : $i]:
% 1.64/1.84         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 1.64/1.84      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.64/1.84  thf('12', plain,
% 1.64/1.84      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 1.64/1.84         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.64/1.84               (k3_subset_1 @ sk_A @ sk_B))))),
% 1.64/1.84      inference('sup-', [status(thm)], ['10', '11'])).
% 1.64/1.84  thf('13', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.64/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.84  thf('14', plain,
% 1.64/1.84      (![X48 : $i, X49 : $i]:
% 1.64/1.84         (((k3_subset_1 @ X48 @ X49) = (k4_xboole_0 @ X48 @ X49))
% 1.64/1.84          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X48)))),
% 1.64/1.84      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.64/1.84  thf('15', plain,
% 1.64/1.84      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 1.64/1.84      inference('sup-', [status(thm)], ['13', '14'])).
% 1.64/1.84  thf(t39_xboole_1, axiom,
% 1.64/1.84    (![A:$i,B:$i]:
% 1.64/1.84     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.64/1.84  thf('16', plain,
% 1.64/1.84      (![X16 : $i, X17 : $i]:
% 1.64/1.84         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 1.64/1.84           = (k2_xboole_0 @ X16 @ X17))),
% 1.64/1.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.64/1.84  thf('17', plain,
% 1.64/1.84      (((k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 1.64/1.84         = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 1.64/1.84      inference('sup+', [status(thm)], ['15', '16'])).
% 1.64/1.84  thf('18', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.64/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.84  thf(d2_subset_1, axiom,
% 1.64/1.84    (![A:$i,B:$i]:
% 1.64/1.84     ( ( ( v1_xboole_0 @ A ) =>
% 1.64/1.84         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.64/1.84       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.64/1.84         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.64/1.84  thf('19', plain,
% 1.64/1.84      (![X45 : $i, X46 : $i]:
% 1.64/1.84         (~ (m1_subset_1 @ X45 @ X46)
% 1.64/1.84          | (r2_hidden @ X45 @ X46)
% 1.64/1.84          | (v1_xboole_0 @ X46))),
% 1.64/1.84      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.64/1.84  thf('20', plain,
% 1.64/1.84      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.64/1.84        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.64/1.84      inference('sup-', [status(thm)], ['18', '19'])).
% 1.64/1.84  thf(fc1_subset_1, axiom,
% 1.64/1.84    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.64/1.84  thf('21', plain, (![X50 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X50))),
% 1.64/1.84      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.64/1.84  thf('22', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.64/1.84      inference('clc', [status(thm)], ['20', '21'])).
% 1.64/1.84  thf(d1_zfmisc_1, axiom,
% 1.64/1.84    (![A:$i,B:$i]:
% 1.64/1.84     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.64/1.84       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.64/1.84  thf('23', plain,
% 1.64/1.84      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.64/1.84         (~ (r2_hidden @ X41 @ X40)
% 1.64/1.84          | (r1_tarski @ X41 @ X39)
% 1.64/1.84          | ((X40) != (k1_zfmisc_1 @ X39)))),
% 1.64/1.84      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.64/1.84  thf('24', plain,
% 1.64/1.84      (![X39 : $i, X41 : $i]:
% 1.64/1.84         ((r1_tarski @ X41 @ X39) | ~ (r2_hidden @ X41 @ (k1_zfmisc_1 @ X39)))),
% 1.64/1.84      inference('simplify', [status(thm)], ['23'])).
% 1.64/1.84  thf('25', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 1.64/1.84      inference('sup-', [status(thm)], ['22', '24'])).
% 1.64/1.84  thf(t36_xboole_1, axiom,
% 1.64/1.84    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.64/1.84  thf('26', plain,
% 1.64/1.84      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 1.64/1.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.64/1.84  thf(t1_xboole_1, axiom,
% 1.64/1.84    (![A:$i,B:$i,C:$i]:
% 1.64/1.84     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.64/1.84       ( r1_tarski @ A @ C ) ))).
% 1.64/1.84  thf('27', plain,
% 1.64/1.84      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.64/1.84         (~ (r1_tarski @ X11 @ X12)
% 1.64/1.84          | ~ (r1_tarski @ X12 @ X13)
% 1.64/1.84          | (r1_tarski @ X11 @ X13))),
% 1.64/1.84      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.64/1.84  thf('28', plain,
% 1.64/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.84         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 1.64/1.84      inference('sup-', [status(thm)], ['26', '27'])).
% 1.64/1.84  thf('29', plain,
% 1.64/1.84      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C_1 @ X0) @ sk_A)),
% 1.64/1.84      inference('sup-', [status(thm)], ['25', '28'])).
% 1.64/1.84  thf(t79_xboole_1, axiom,
% 1.64/1.84    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.64/1.84  thf('30', plain,
% 1.64/1.84      (![X24 : $i, X25 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ X25)),
% 1.64/1.84      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.64/1.84  thf(t69_xboole_1, axiom,
% 1.64/1.84    (![A:$i,B:$i]:
% 1.64/1.84     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.64/1.84       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 1.64/1.84  thf('31', plain,
% 1.64/1.84      (![X19 : $i, X20 : $i]:
% 1.64/1.84         (~ (r1_xboole_0 @ X19 @ X20)
% 1.64/1.84          | ~ (r1_tarski @ X19 @ X20)
% 1.64/1.84          | (v1_xboole_0 @ X19))),
% 1.64/1.84      inference('cnf', [status(esa)], [t69_xboole_1])).
% 1.64/1.84  thf('32', plain,
% 1.64/1.84      (![X0 : $i, X1 : $i]:
% 1.64/1.84         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 1.64/1.84          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.64/1.84      inference('sup-', [status(thm)], ['30', '31'])).
% 1.64/1.84  thf('33', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 1.64/1.84      inference('sup-', [status(thm)], ['29', '32'])).
% 1.64/1.84  thf(l13_xboole_0, axiom,
% 1.64/1.84    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.64/1.84  thf('34', plain,
% 1.64/1.84      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 1.64/1.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.64/1.84  thf('35', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 1.64/1.84      inference('sup-', [status(thm)], ['33', '34'])).
% 1.64/1.84  thf('36', plain,
% 1.64/1.84      (![X16 : $i, X17 : $i]:
% 1.64/1.84         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 1.64/1.84           = (k2_xboole_0 @ X16 @ X17))),
% 1.64/1.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.64/1.84  thf('37', plain,
% 1.64/1.84      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_C_1))),
% 1.64/1.84      inference('sup+', [status(thm)], ['35', '36'])).
% 1.64/1.84  thf(commutativity_k2_tarski, axiom,
% 1.64/1.84    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.64/1.84  thf('38', plain,
% 1.64/1.84      (![X34 : $i, X35 : $i]:
% 1.64/1.84         ((k2_tarski @ X35 @ X34) = (k2_tarski @ X34 @ X35))),
% 1.64/1.84      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.64/1.84  thf(l51_zfmisc_1, axiom,
% 1.64/1.84    (![A:$i,B:$i]:
% 1.64/1.84     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.64/1.84  thf('39', plain,
% 1.64/1.84      (![X43 : $i, X44 : $i]:
% 1.64/1.84         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 1.64/1.84      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.64/1.84  thf('40', plain,
% 1.64/1.84      (![X0 : $i, X1 : $i]:
% 1.64/1.84         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.64/1.84      inference('sup+', [status(thm)], ['38', '39'])).
% 1.64/1.84  thf('41', plain,
% 1.64/1.84      (![X43 : $i, X44 : $i]:
% 1.64/1.84         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 1.64/1.84      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.64/1.84  thf('42', plain,
% 1.64/1.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.64/1.84      inference('sup+', [status(thm)], ['40', '41'])).
% 1.64/1.84  thf('43', plain,
% 1.64/1.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.64/1.84      inference('sup+', [status(thm)], ['40', '41'])).
% 1.64/1.84  thf(t1_boole, axiom,
% 1.64/1.84    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.64/1.84  thf('44', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.64/1.84      inference('cnf', [status(esa)], [t1_boole])).
% 1.64/1.84  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.64/1.84      inference('sup+', [status(thm)], ['43', '44'])).
% 1.64/1.84  thf('46', plain,
% 1.64/1.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.64/1.84      inference('sup+', [status(thm)], ['40', '41'])).
% 1.64/1.84  thf('47', plain, (((sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 1.64/1.84      inference('demod', [status(thm)], ['37', '42', '45', '46'])).
% 1.64/1.84  thf('48', plain,
% 1.64/1.84      (((k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_C_1)) = (sk_A))),
% 1.64/1.84      inference('demod', [status(thm)], ['17', '47'])).
% 1.64/1.84  thf(t73_xboole_1, axiom,
% 1.64/1.84    (![A:$i,B:$i,C:$i]:
% 1.64/1.84     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 1.64/1.84       ( r1_tarski @ A @ B ) ))).
% 1.64/1.84  thf('49', plain,
% 1.64/1.84      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.64/1.84         ((r1_tarski @ X21 @ X22)
% 1.64/1.84          | ~ (r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 1.64/1.84          | ~ (r1_xboole_0 @ X21 @ X23))),
% 1.64/1.84      inference('cnf', [status(esa)], [t73_xboole_1])).
% 1.64/1.84  thf('50', plain,
% 1.64/1.84      (![X0 : $i]:
% 1.64/1.84         (~ (r1_tarski @ X0 @ sk_A)
% 1.64/1.84          | ~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 1.64/1.84          | (r1_tarski @ X0 @ sk_C_1))),
% 1.64/1.84      inference('sup-', [status(thm)], ['48', '49'])).
% 1.64/1.84  thf('51', plain,
% 1.64/1.84      ((((r1_tarski @ sk_B @ sk_C_1) | ~ (r1_tarski @ sk_B @ sk_A)))
% 1.64/1.84         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.64/1.84               (k3_subset_1 @ sk_A @ sk_B))))),
% 1.64/1.84      inference('sup-', [status(thm)], ['12', '50'])).
% 1.64/1.84  thf('52', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.64/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.84  thf('53', plain,
% 1.64/1.84      (![X45 : $i, X46 : $i]:
% 1.64/1.84         (~ (m1_subset_1 @ X45 @ X46)
% 1.64/1.84          | (r2_hidden @ X45 @ X46)
% 1.64/1.84          | (v1_xboole_0 @ X46))),
% 1.64/1.84      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.64/1.84  thf('54', plain,
% 1.64/1.84      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.64/1.84        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 1.64/1.84      inference('sup-', [status(thm)], ['52', '53'])).
% 1.64/1.84  thf('55', plain, (![X50 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X50))),
% 1.64/1.84      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.64/1.84  thf('56', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.64/1.84      inference('clc', [status(thm)], ['54', '55'])).
% 1.64/1.84  thf('57', plain,
% 1.64/1.84      (![X39 : $i, X41 : $i]:
% 1.64/1.84         ((r1_tarski @ X41 @ X39) | ~ (r2_hidden @ X41 @ (k1_zfmisc_1 @ X39)))),
% 1.64/1.84      inference('simplify', [status(thm)], ['23'])).
% 1.64/1.84  thf('58', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.64/1.84      inference('sup-', [status(thm)], ['56', '57'])).
% 1.64/1.84  thf('59', plain,
% 1.64/1.84      (((r1_tarski @ sk_B @ sk_C_1))
% 1.64/1.84         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.64/1.84               (k3_subset_1 @ sk_A @ sk_B))))),
% 1.64/1.84      inference('demod', [status(thm)], ['51', '58'])).
% 1.64/1.84  thf('60', plain,
% 1.64/1.84      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 1.64/1.84      inference('split', [status(esa)], ['0'])).
% 1.64/1.84  thf('61', plain,
% 1.64/1.84      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 1.64/1.84       ~
% 1.64/1.84       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.64/1.84         (k3_subset_1 @ sk_A @ sk_B)))),
% 1.64/1.84      inference('sup-', [status(thm)], ['59', '60'])).
% 1.64/1.84  thf('62', plain,
% 1.64/1.84      (~
% 1.64/1.84       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.64/1.84         (k3_subset_1 @ sk_A @ sk_B)))),
% 1.64/1.84      inference('sat_resolution*', [status(thm)], ['2', '61'])).
% 1.64/1.84  thf('63', plain,
% 1.64/1.84      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.64/1.84          (k3_subset_1 @ sk_A @ sk_B))),
% 1.64/1.84      inference('simpl_trail', [status(thm)], ['1', '62'])).
% 1.64/1.84  thf('64', plain,
% 1.64/1.84      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.64/1.84      inference('sup-', [status(thm)], ['5', '6'])).
% 1.64/1.84  thf('65', plain,
% 1.64/1.84      (![X16 : $i, X17 : $i]:
% 1.64/1.84         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 1.64/1.84           = (k2_xboole_0 @ X16 @ X17))),
% 1.64/1.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.64/1.84  thf('66', plain,
% 1.64/1.84      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 1.64/1.84         = (k2_xboole_0 @ sk_B @ sk_A))),
% 1.64/1.84      inference('sup+', [status(thm)], ['64', '65'])).
% 1.64/1.84  thf('67', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.64/1.84      inference('sup-', [status(thm)], ['56', '57'])).
% 1.64/1.84  thf('68', plain,
% 1.64/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.84         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 1.64/1.84      inference('sup-', [status(thm)], ['26', '27'])).
% 1.64/1.84  thf('69', plain,
% 1.64/1.84      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 1.64/1.84      inference('sup-', [status(thm)], ['67', '68'])).
% 1.64/1.84  thf('70', plain,
% 1.64/1.84      (![X0 : $i, X1 : $i]:
% 1.64/1.84         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 1.64/1.84          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.64/1.84      inference('sup-', [status(thm)], ['30', '31'])).
% 1.64/1.84  thf('71', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A))),
% 1.64/1.84      inference('sup-', [status(thm)], ['69', '70'])).
% 1.64/1.84  thf('72', plain,
% 1.64/1.84      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 1.64/1.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.64/1.84  thf('73', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.64/1.84      inference('sup-', [status(thm)], ['71', '72'])).
% 1.64/1.84  thf('74', plain,
% 1.64/1.84      (![X16 : $i, X17 : $i]:
% 1.64/1.84         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 1.64/1.84           = (k2_xboole_0 @ X16 @ X17))),
% 1.64/1.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.64/1.84  thf('75', plain,
% 1.64/1.84      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 1.64/1.84      inference('sup+', [status(thm)], ['73', '74'])).
% 1.64/1.84  thf('76', plain,
% 1.64/1.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.64/1.84      inference('sup+', [status(thm)], ['40', '41'])).
% 1.64/1.84  thf('77', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.64/1.84      inference('sup+', [status(thm)], ['43', '44'])).
% 1.64/1.84  thf('78', plain,
% 1.64/1.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.64/1.84      inference('sup+', [status(thm)], ['40', '41'])).
% 1.64/1.84  thf('79', plain, (((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 1.64/1.84      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 1.64/1.84  thf('80', plain,
% 1.64/1.84      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 1.64/1.84      inference('demod', [status(thm)], ['66', '79'])).
% 1.64/1.84  thf('81', plain,
% 1.64/1.84      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 1.64/1.84      inference('split', [status(esa)], ['3'])).
% 1.64/1.84  thf(t85_xboole_1, axiom,
% 1.64/1.84    (![A:$i,B:$i,C:$i]:
% 1.64/1.84     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 1.64/1.84  thf('82', plain,
% 1.64/1.84      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.64/1.84         (~ (r1_tarski @ X26 @ X27)
% 1.64/1.84          | (r1_xboole_0 @ X26 @ (k4_xboole_0 @ X28 @ X27)))),
% 1.64/1.84      inference('cnf', [status(esa)], [t85_xboole_1])).
% 1.64/1.84  thf('83', plain,
% 1.64/1.84      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1)))
% 1.64/1.84         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 1.64/1.84      inference('sup-', [status(thm)], ['81', '82'])).
% 1.64/1.84  thf('84', plain,
% 1.64/1.84      (![X3 : $i, X4 : $i]:
% 1.64/1.84         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 1.64/1.84      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.64/1.84  thf('85', plain,
% 1.64/1.84      ((![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_B))
% 1.64/1.84         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 1.64/1.84      inference('sup-', [status(thm)], ['83', '84'])).
% 1.64/1.84  thf('86', plain,
% 1.64/1.84      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 1.64/1.84       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.64/1.84         (k3_subset_1 @ sk_A @ sk_B)))),
% 1.64/1.84      inference('split', [status(esa)], ['3'])).
% 1.64/1.84  thf('87', plain, (((r1_tarski @ sk_B @ sk_C_1))),
% 1.64/1.84      inference('sat_resolution*', [status(thm)], ['2', '61', '86'])).
% 1.64/1.84  thf('88', plain,
% 1.64/1.84      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_B)),
% 1.64/1.84      inference('simpl_trail', [status(thm)], ['85', '87'])).
% 1.64/1.84  thf('89', plain,
% 1.64/1.84      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 1.64/1.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.64/1.84  thf('90', plain,
% 1.64/1.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.64/1.84      inference('sup+', [status(thm)], ['40', '41'])).
% 1.64/1.84  thf('91', plain,
% 1.64/1.84      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.64/1.84         ((r1_tarski @ X21 @ X22)
% 1.64/1.84          | ~ (r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 1.64/1.84          | ~ (r1_xboole_0 @ X21 @ X23))),
% 1.64/1.84      inference('cnf', [status(esa)], [t73_xboole_1])).
% 1.64/1.84  thf('92', plain,
% 1.64/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.84         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.64/1.84          | ~ (r1_xboole_0 @ X2 @ X1)
% 1.64/1.84          | (r1_tarski @ X2 @ X0))),
% 1.64/1.84      inference('sup-', [status(thm)], ['90', '91'])).
% 1.64/1.84  thf('93', plain,
% 1.64/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.84         ((r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X0)
% 1.64/1.84          | ~ (r1_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1))),
% 1.64/1.84      inference('sup-', [status(thm)], ['89', '92'])).
% 1.64/1.84  thf('94', plain,
% 1.64/1.84      (![X0 : $i]:
% 1.64/1.84         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ sk_C_1) @ X0)),
% 1.64/1.84      inference('sup-', [status(thm)], ['88', '93'])).
% 1.64/1.84  thf('95', plain,
% 1.64/1.84      ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ (k3_subset_1 @ sk_A @ sk_B))),
% 1.64/1.84      inference('sup+', [status(thm)], ['80', '94'])).
% 1.64/1.84  thf('96', plain,
% 1.64/1.84      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 1.64/1.84      inference('sup-', [status(thm)], ['13', '14'])).
% 1.64/1.84  thf('97', plain,
% 1.64/1.84      ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k3_subset_1 @ sk_A @ sk_B))),
% 1.64/1.84      inference('demod', [status(thm)], ['95', '96'])).
% 1.64/1.84  thf('98', plain, ($false), inference('demod', [status(thm)], ['63', '97'])).
% 1.64/1.84  
% 1.64/1.84  % SZS output end Refutation
% 1.64/1.84  
% 1.64/1.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
