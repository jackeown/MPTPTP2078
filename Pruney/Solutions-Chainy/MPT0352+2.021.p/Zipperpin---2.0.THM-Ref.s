%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m7Vl1rdSPT

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:10 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 396 expanded)
%              Number of leaves         :   29 ( 135 expanded)
%              Depth                    :   27
%              Number of atoms          : 1441 (3374 expanded)
%              Number of equality atoms :  129 ( 298 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('7',plain,
    ( ( ( k2_xboole_0 @ sk_C @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_C @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,
    ( ( sk_C
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['7','8','11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k3_subset_1 @ X47 @ X48 )
        = ( k4_xboole_0 @ X47 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X26 @ X27 ) @ X28 )
      = ( k4_xboole_0 @ X26 @ ( k2_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C )
      = ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k3_subset_1 @ X47 @ X48 )
        = ( k4_xboole_0 @ X47 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('22',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C )
      = ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('24',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X37 @ X38 ) @ ( k4_xboole_0 @ X37 @ X38 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['24','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['23','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('38',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X49: $i,X50: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X49 @ X50 ) @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('41',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k3_subset_1 @ X47 @ X48 )
        = ( k4_xboole_0 @ X47 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('43',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['24','30'])).

thf('45',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ sk_A ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('47',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k3_subset_1 @ X52 @ ( k3_subset_1 @ X52 @ X51 ) )
        = X51 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('48',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('53',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('57',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['38','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X24 @ X25 ) @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('64',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('65',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k4_xboole_0 @ X31 @ ( k4_xboole_0 @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('67',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('68',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('72',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('73',plain,
    ( ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(t111_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('74',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X6 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t111_xboole_1])).

thf('75',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ X0 ) @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X6 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t111_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r1_tarski @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ X0 ) @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ X0 ) @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B ) @ k1_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['70','84'])).

thf('86',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('87',plain,
    ( ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B ) @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('89',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','92'])).

thf('94',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_C @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['38','57'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('100',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k4_xboole_0 @ X31 @ ( k4_xboole_0 @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('103',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','109'])).

thf('111',plain,(
    r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['98','110'])).

thf('112',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('113',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('115',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('120',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k3_xboole_0 @ X33 @ ( k4_xboole_0 @ X34 @ X35 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('122',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['115','116','117','118','127'])).

thf('129',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','128'])).

thf('130',plain,
    ( ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('132',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_B ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('134',plain,
    ( ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_B ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('139',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_B )
      = sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('141',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['139','142'])).

thf('144',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
   <= ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('145',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','34','35','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m7Vl1rdSPT
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:31:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.99/1.22  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.22  % Solved by: fo/fo7.sh
% 0.99/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.22  % done 1710 iterations in 0.752s
% 0.99/1.22  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.22  % SZS output start Refutation
% 0.99/1.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.22  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.22  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.22  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.99/1.22  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.99/1.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.22  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.22  thf(sk_C_type, type, sk_C: $i).
% 0.99/1.22  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.99/1.22  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.22  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.99/1.22  thf(t31_subset_1, conjecture,
% 0.99/1.22    (![A:$i,B:$i]:
% 0.99/1.22     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.22       ( ![C:$i]:
% 0.99/1.22         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.22           ( ( r1_tarski @ B @ C ) <=>
% 0.99/1.22             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.99/1.22  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.22    (~( ![A:$i,B:$i]:
% 0.99/1.22        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.22          ( ![C:$i]:
% 0.99/1.22            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.22              ( ( r1_tarski @ B @ C ) <=>
% 0.99/1.22                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.99/1.22    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.99/1.22  thf('0', plain,
% 0.99/1.22      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22           (k3_subset_1 @ sk_A @ sk_B))
% 0.99/1.22        | ~ (r1_tarski @ sk_B @ sk_C))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('1', plain,
% 0.99/1.22      (~
% 0.99/1.22       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.99/1.22       ~ ((r1_tarski @ sk_B @ sk_C))),
% 0.99/1.22      inference('split', [status(esa)], ['0'])).
% 0.99/1.22  thf('2', plain,
% 0.99/1.22      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))
% 0.99/1.22        | (r1_tarski @ sk_B @ sk_C))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('3', plain,
% 0.99/1.22      (((r1_tarski @ sk_B @ sk_C)) <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.99/1.22      inference('split', [status(esa)], ['2'])).
% 0.99/1.22  thf(l32_xboole_1, axiom,
% 0.99/1.22    (![A:$i,B:$i]:
% 0.99/1.22     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.99/1.22  thf('4', plain,
% 0.99/1.22      (![X3 : $i, X5 : $i]:
% 0.99/1.22         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.99/1.22      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.99/1.22  thf('5', plain,
% 0.99/1.22      ((((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0)))
% 0.99/1.22         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.99/1.22      inference('sup-', [status(thm)], ['3', '4'])).
% 0.99/1.22  thf(t39_xboole_1, axiom,
% 0.99/1.22    (![A:$i,B:$i]:
% 0.99/1.22     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.99/1.22  thf('6', plain,
% 0.99/1.22      (![X22 : $i, X23 : $i]:
% 0.99/1.22         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 0.99/1.22           = (k2_xboole_0 @ X22 @ X23))),
% 0.99/1.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.99/1.22  thf('7', plain,
% 0.99/1.22      ((((k2_xboole_0 @ sk_C @ k1_xboole_0) = (k2_xboole_0 @ sk_C @ sk_B)))
% 0.99/1.22         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.99/1.22      inference('sup+', [status(thm)], ['5', '6'])).
% 0.99/1.22  thf(commutativity_k2_xboole_0, axiom,
% 0.99/1.22    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.99/1.22  thf('8', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.22  thf('9', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.22  thf(t1_boole, axiom,
% 0.99/1.22    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.99/1.22  thf('10', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.99/1.22      inference('cnf', [status(esa)], [t1_boole])).
% 0.99/1.22  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['9', '10'])).
% 0.99/1.22  thf('12', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.22  thf('13', plain,
% 0.99/1.22      ((((sk_C) = (k2_xboole_0 @ sk_B @ sk_C)))
% 0.99/1.22         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.99/1.22      inference('demod', [status(thm)], ['7', '8', '11', '12'])).
% 0.99/1.22  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf(d5_subset_1, axiom,
% 0.99/1.22    (![A:$i,B:$i]:
% 0.99/1.22     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.22       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.99/1.22  thf('15', plain,
% 0.99/1.22      (![X47 : $i, X48 : $i]:
% 0.99/1.22         (((k3_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))
% 0.99/1.22          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X47)))),
% 0.99/1.22      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.99/1.22  thf('16', plain,
% 0.99/1.22      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.99/1.22      inference('sup-', [status(thm)], ['14', '15'])).
% 0.99/1.22  thf(t41_xboole_1, axiom,
% 0.99/1.22    (![A:$i,B:$i,C:$i]:
% 0.99/1.22     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.99/1.22       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.99/1.22  thf('17', plain,
% 0.99/1.22      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.99/1.22         ((k4_xboole_0 @ (k4_xboole_0 @ X26 @ X27) @ X28)
% 0.99/1.22           = (k4_xboole_0 @ X26 @ (k2_xboole_0 @ X27 @ X28)))),
% 0.99/1.22      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.99/1.22  thf('18', plain,
% 0.99/1.22      (![X0 : $i]:
% 0.99/1.22         ((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 0.99/1.22           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.99/1.22      inference('sup+', [status(thm)], ['16', '17'])).
% 0.99/1.22  thf('19', plain,
% 0.99/1.22      ((((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C)
% 0.99/1.22          = (k4_xboole_0 @ sk_A @ sk_C)))
% 0.99/1.22         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.99/1.22      inference('sup+', [status(thm)], ['13', '18'])).
% 0.99/1.22  thf('20', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('21', plain,
% 0.99/1.22      (![X47 : $i, X48 : $i]:
% 0.99/1.22         (((k3_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))
% 0.99/1.22          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X47)))),
% 0.99/1.22      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.99/1.22  thf('22', plain,
% 0.99/1.22      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.99/1.22      inference('sup-', [status(thm)], ['20', '21'])).
% 0.99/1.22  thf('23', plain,
% 0.99/1.22      ((((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C)
% 0.99/1.22          = (k3_subset_1 @ sk_A @ sk_C)))
% 0.99/1.22         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.99/1.22      inference('demod', [status(thm)], ['19', '22'])).
% 0.99/1.22  thf(t51_xboole_1, axiom,
% 0.99/1.22    (![A:$i,B:$i]:
% 0.99/1.22     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.99/1.22       ( A ) ))).
% 0.99/1.22  thf('24', plain,
% 0.99/1.22      (![X37 : $i, X38 : $i]:
% 0.99/1.22         ((k2_xboole_0 @ (k3_xboole_0 @ X37 @ X38) @ (k4_xboole_0 @ X37 @ X38))
% 0.99/1.22           = (X37))),
% 0.99/1.22      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.99/1.22  thf('25', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.22  thf(t46_xboole_1, axiom,
% 0.99/1.22    (![A:$i,B:$i]:
% 0.99/1.22     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.99/1.22  thf('26', plain,
% 0.99/1.22      (![X29 : $i, X30 : $i]:
% 0.99/1.22         ((k4_xboole_0 @ X29 @ (k2_xboole_0 @ X29 @ X30)) = (k1_xboole_0))),
% 0.99/1.22      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.99/1.22  thf('27', plain,
% 0.99/1.22      (![X3 : $i, X4 : $i]:
% 0.99/1.22         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.99/1.22      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.99/1.22  thf('28', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]:
% 0.99/1.22         (((k1_xboole_0) != (k1_xboole_0))
% 0.99/1.22          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.99/1.22      inference('sup-', [status(thm)], ['26', '27'])).
% 0.99/1.22  thf('29', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.99/1.22      inference('simplify', [status(thm)], ['28'])).
% 0.99/1.22  thf('30', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['25', '29'])).
% 0.99/1.22  thf('31', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.99/1.22      inference('sup+', [status(thm)], ['24', '30'])).
% 0.99/1.22  thf('32', plain,
% 0.99/1.22      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.99/1.22         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.99/1.22      inference('sup+', [status(thm)], ['23', '31'])).
% 0.99/1.22  thf('33', plain,
% 0.99/1.22      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22           (k3_subset_1 @ sk_A @ sk_B)))
% 0.99/1.22         <= (~
% 0.99/1.22             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('split', [status(esa)], ['0'])).
% 0.99/1.22  thf('34', plain,
% 0.99/1.22      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.99/1.22       ~ ((r1_tarski @ sk_B @ sk_C))),
% 0.99/1.22      inference('sup-', [status(thm)], ['32', '33'])).
% 0.99/1.22  thf('35', plain,
% 0.99/1.22      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.99/1.22       ((r1_tarski @ sk_B @ sk_C))),
% 0.99/1.22      inference('split', [status(esa)], ['2'])).
% 0.99/1.22  thf('36', plain,
% 0.99/1.22      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.99/1.22      inference('sup-', [status(thm)], ['14', '15'])).
% 0.99/1.22  thf('37', plain,
% 0.99/1.22      (![X22 : $i, X23 : $i]:
% 0.99/1.22         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 0.99/1.22           = (k2_xboole_0 @ X22 @ X23))),
% 0.99/1.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.99/1.22  thf('38', plain,
% 0.99/1.22      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.99/1.22         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.99/1.22      inference('sup+', [status(thm)], ['36', '37'])).
% 0.99/1.22  thf('39', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf(dt_k3_subset_1, axiom,
% 0.99/1.22    (![A:$i,B:$i]:
% 0.99/1.22     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.22       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.99/1.22  thf('40', plain,
% 0.99/1.22      (![X49 : $i, X50 : $i]:
% 0.99/1.22         ((m1_subset_1 @ (k3_subset_1 @ X49 @ X50) @ (k1_zfmisc_1 @ X49))
% 0.99/1.22          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X49)))),
% 0.99/1.22      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.99/1.22  thf('41', plain,
% 0.99/1.22      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.99/1.22      inference('sup-', [status(thm)], ['39', '40'])).
% 0.99/1.22  thf('42', plain,
% 0.99/1.22      (![X47 : $i, X48 : $i]:
% 0.99/1.22         (((k3_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))
% 0.99/1.22          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X47)))),
% 0.99/1.22      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.99/1.22  thf('43', plain,
% 0.99/1.22      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.99/1.22         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.99/1.22      inference('sup-', [status(thm)], ['41', '42'])).
% 0.99/1.22  thf('44', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.99/1.22      inference('sup+', [status(thm)], ['24', '30'])).
% 0.99/1.22  thf('45', plain,
% 0.99/1.22      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) @ sk_A)),
% 0.99/1.22      inference('sup+', [status(thm)], ['43', '44'])).
% 0.99/1.22  thf('46', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf(involutiveness_k3_subset_1, axiom,
% 0.99/1.22    (![A:$i,B:$i]:
% 0.99/1.22     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.22       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.99/1.22  thf('47', plain,
% 0.99/1.22      (![X51 : $i, X52 : $i]:
% 0.99/1.22         (((k3_subset_1 @ X52 @ (k3_subset_1 @ X52 @ X51)) = (X51))
% 0.99/1.22          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X52)))),
% 0.99/1.22      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.99/1.22  thf('48', plain,
% 0.99/1.22      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.99/1.22      inference('sup-', [status(thm)], ['46', '47'])).
% 0.99/1.22  thf('49', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.99/1.22      inference('demod', [status(thm)], ['45', '48'])).
% 0.99/1.22  thf('50', plain,
% 0.99/1.22      (![X3 : $i, X5 : $i]:
% 0.99/1.22         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.99/1.22      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.99/1.22  thf('51', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.99/1.22      inference('sup-', [status(thm)], ['49', '50'])).
% 0.99/1.22  thf('52', plain,
% 0.99/1.22      (![X22 : $i, X23 : $i]:
% 0.99/1.22         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 0.99/1.22           = (k2_xboole_0 @ X22 @ X23))),
% 0.99/1.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.99/1.22  thf('53', plain,
% 0.99/1.22      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.99/1.22      inference('sup+', [status(thm)], ['51', '52'])).
% 0.99/1.22  thf('54', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.22  thf('55', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['9', '10'])).
% 0.99/1.22  thf('56', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.22  thf('57', plain, (((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.99/1.22      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.99/1.22  thf('58', plain,
% 0.99/1.22      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.99/1.22      inference('demod', [status(thm)], ['38', '57'])).
% 0.99/1.22  thf('59', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.22  thf(t40_xboole_1, axiom,
% 0.99/1.22    (![A:$i,B:$i]:
% 0.99/1.22     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.99/1.22  thf('60', plain,
% 0.99/1.22      (![X24 : $i, X25 : $i]:
% 0.99/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X24 @ X25) @ X25)
% 0.99/1.22           = (k4_xboole_0 @ X24 @ X25))),
% 0.99/1.22      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.99/1.22  thf('61', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]:
% 0.99/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.99/1.22           = (k4_xboole_0 @ X0 @ X1))),
% 0.99/1.22      inference('sup+', [status(thm)], ['59', '60'])).
% 0.99/1.22  thf('62', plain,
% 0.99/1.22      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.99/1.22         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.99/1.22      inference('sup+', [status(thm)], ['58', '61'])).
% 0.99/1.22  thf('63', plain,
% 0.99/1.22      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.99/1.22      inference('sup-', [status(thm)], ['14', '15'])).
% 0.99/1.22  thf('64', plain,
% 0.99/1.22      (((k3_subset_1 @ sk_A @ sk_B)
% 0.99/1.22         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.99/1.22      inference('demod', [status(thm)], ['62', '63'])).
% 0.99/1.22  thf(t48_xboole_1, axiom,
% 0.99/1.22    (![A:$i,B:$i]:
% 0.99/1.22     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.99/1.22  thf('65', plain,
% 0.99/1.22      (![X31 : $i, X32 : $i]:
% 0.99/1.22         ((k4_xboole_0 @ X31 @ (k4_xboole_0 @ X31 @ X32))
% 0.99/1.22           = (k3_xboole_0 @ X31 @ X32))),
% 0.99/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.22  thf('66', plain,
% 0.99/1.22      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.99/1.22         (k3_subset_1 @ sk_A @ sk_B))
% 0.99/1.22         = (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.99/1.22      inference('sup+', [status(thm)], ['64', '65'])).
% 0.99/1.22  thf(idempotence_k2_xboole_0, axiom,
% 0.99/1.22    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.99/1.22  thf('67', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.99/1.22      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.99/1.22  thf('68', plain,
% 0.99/1.22      (![X29 : $i, X30 : $i]:
% 0.99/1.22         ((k4_xboole_0 @ X29 @ (k2_xboole_0 @ X29 @ X30)) = (k1_xboole_0))),
% 0.99/1.22      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.99/1.22  thf('69', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['67', '68'])).
% 0.99/1.22  thf('70', plain,
% 0.99/1.22      (((k1_xboole_0) = (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.99/1.22      inference('demod', [status(thm)], ['66', '69'])).
% 0.99/1.22  thf('71', plain,
% 0.99/1.22      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.99/1.22         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('split', [status(esa)], ['2'])).
% 0.99/1.22  thf('72', plain,
% 0.99/1.22      (![X3 : $i, X5 : $i]:
% 0.99/1.22         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.99/1.22      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.99/1.22  thf('73', plain,
% 0.99/1.22      ((((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22          (k3_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0)))
% 0.99/1.22         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('sup-', [status(thm)], ['71', '72'])).
% 0.99/1.22  thf(t111_xboole_1, axiom,
% 0.99/1.22    (![A:$i,B:$i,C:$i]:
% 0.99/1.22     ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.99/1.22       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.99/1.22  thf('74', plain,
% 0.99/1.22      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.99/1.22         ((k4_xboole_0 @ (k3_xboole_0 @ X6 @ X8) @ (k3_xboole_0 @ X7 @ X8))
% 0.99/1.22           = (k3_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8))),
% 0.99/1.22      inference('cnf', [status(esa)], [t111_xboole_1])).
% 0.99/1.22  thf('75', plain,
% 0.99/1.22      (![X3 : $i, X4 : $i]:
% 0.99/1.22         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.99/1.22      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.99/1.22  thf('76', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.22         (((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 0.99/1.22          | (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.99/1.22      inference('sup-', [status(thm)], ['74', '75'])).
% 0.99/1.22  thf('77', plain,
% 0.99/1.22      ((![X0 : $i]:
% 0.99/1.22          (((k3_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.99/1.22           | (r1_tarski @ (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ X0) @ 
% 0.99/1.22              (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0))))
% 0.99/1.22         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('sup-', [status(thm)], ['73', '76'])).
% 0.99/1.22  thf('78', plain,
% 0.99/1.22      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.99/1.22         ((k4_xboole_0 @ (k3_xboole_0 @ X6 @ X8) @ (k3_xboole_0 @ X7 @ X8))
% 0.99/1.22           = (k3_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8))),
% 0.99/1.22      inference('cnf', [status(esa)], [t111_xboole_1])).
% 0.99/1.22  thf('79', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['67', '68'])).
% 0.99/1.22  thf('80', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]:
% 0.99/1.22         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['78', '79'])).
% 0.99/1.22  thf('81', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['67', '68'])).
% 0.99/1.22  thf('82', plain,
% 0.99/1.22      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.99/1.22      inference('demod', [status(thm)], ['80', '81'])).
% 0.99/1.22  thf('83', plain,
% 0.99/1.22      ((![X0 : $i]:
% 0.99/1.22          (((k1_xboole_0) != (k1_xboole_0))
% 0.99/1.22           | (r1_tarski @ (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ X0) @ 
% 0.99/1.22              (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0))))
% 0.99/1.22         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('demod', [status(thm)], ['77', '82'])).
% 0.99/1.22  thf('84', plain,
% 0.99/1.22      ((![X0 : $i]:
% 0.99/1.22          (r1_tarski @ (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ X0) @ 
% 0.99/1.22           (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)))
% 0.99/1.22         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('simplify', [status(thm)], ['83'])).
% 0.99/1.22  thf('85', plain,
% 0.99/1.22      (((r1_tarski @ (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B) @ 
% 0.99/1.22         k1_xboole_0))
% 0.99/1.22         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('sup+', [status(thm)], ['70', '84'])).
% 0.99/1.22  thf('86', plain,
% 0.99/1.22      (![X3 : $i, X5 : $i]:
% 0.99/1.22         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.99/1.22      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.99/1.22  thf('87', plain,
% 0.99/1.22      ((((k4_xboole_0 @ (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B) @ 
% 0.99/1.22          k1_xboole_0) = (k1_xboole_0)))
% 0.99/1.22         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('sup-', [status(thm)], ['85', '86'])).
% 0.99/1.22  thf('88', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['9', '10'])).
% 0.99/1.22  thf('89', plain,
% 0.99/1.22      (![X22 : $i, X23 : $i]:
% 0.99/1.22         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 0.99/1.22           = (k2_xboole_0 @ X22 @ X23))),
% 0.99/1.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.99/1.22  thf('90', plain,
% 0.99/1.22      (![X0 : $i]:
% 0.99/1.22         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['88', '89'])).
% 0.99/1.22  thf('91', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['9', '10'])).
% 0.99/1.22  thf('92', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.99/1.22      inference('demod', [status(thm)], ['90', '91'])).
% 0.99/1.22  thf('93', plain,
% 0.99/1.22      ((((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0)))
% 0.99/1.22         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('demod', [status(thm)], ['87', '92'])).
% 0.99/1.22  thf('94', plain,
% 0.99/1.22      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.99/1.22      inference('sup-', [status(thm)], ['20', '21'])).
% 0.99/1.22  thf('95', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.22         (((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 0.99/1.22          | (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.99/1.22      inference('sup-', [status(thm)], ['74', '75'])).
% 0.99/1.22  thf('96', plain,
% 0.99/1.22      (![X0 : $i]:
% 0.99/1.22         (((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ X0) != (k1_xboole_0))
% 0.99/1.22          | (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.99/1.22      inference('sup-', [status(thm)], ['94', '95'])).
% 0.99/1.22  thf('97', plain,
% 0.99/1.22      (((((k1_xboole_0) != (k1_xboole_0))
% 0.99/1.22         | (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.99/1.22            (k3_xboole_0 @ sk_C @ sk_B))))
% 0.99/1.22         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('sup-', [status(thm)], ['93', '96'])).
% 0.99/1.22  thf('98', plain,
% 0.99/1.22      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.99/1.22      inference('demod', [status(thm)], ['38', '57'])).
% 0.99/1.22  thf('99', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['67', '68'])).
% 0.99/1.22  thf('100', plain,
% 0.99/1.22      (![X31 : $i, X32 : $i]:
% 0.99/1.22         ((k4_xboole_0 @ X31 @ (k4_xboole_0 @ X31 @ X32))
% 0.99/1.22           = (k3_xboole_0 @ X31 @ X32))),
% 0.99/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.22  thf('101', plain,
% 0.99/1.22      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['99', '100'])).
% 0.99/1.22  thf('102', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.99/1.22      inference('demod', [status(thm)], ['90', '91'])).
% 0.99/1.22  thf('103', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.99/1.22      inference('demod', [status(thm)], ['101', '102'])).
% 0.99/1.22  thf('104', plain,
% 0.99/1.22      (![X29 : $i, X30 : $i]:
% 0.99/1.22         ((k4_xboole_0 @ X29 @ (k2_xboole_0 @ X29 @ X30)) = (k1_xboole_0))),
% 0.99/1.22      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.99/1.22  thf('105', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.22         (((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 0.99/1.22          | (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.99/1.22      inference('sup-', [status(thm)], ['74', '75'])).
% 0.99/1.22  thf('106', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.22         (((k3_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.99/1.22          | (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ 
% 0.99/1.22             (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 0.99/1.22      inference('sup-', [status(thm)], ['104', '105'])).
% 0.99/1.22  thf('107', plain,
% 0.99/1.22      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.99/1.22      inference('demod', [status(thm)], ['80', '81'])).
% 0.99/1.22  thf('108', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.22         (((k1_xboole_0) != (k1_xboole_0))
% 0.99/1.22          | (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ 
% 0.99/1.22             (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 0.99/1.22      inference('demod', [status(thm)], ['106', '107'])).
% 0.99/1.22  thf('109', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.22         (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ 
% 0.99/1.22          (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 0.99/1.22      inference('simplify', [status(thm)], ['108'])).
% 0.99/1.22  thf('110', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]:
% 0.99/1.22         (r1_tarski @ X0 @ (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['103', '109'])).
% 0.99/1.22  thf('111', plain, ((r1_tarski @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.99/1.22      inference('sup+', [status(thm)], ['98', '110'])).
% 0.99/1.22  thf('112', plain,
% 0.99/1.22      (![X3 : $i, X5 : $i]:
% 0.99/1.22         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.99/1.22      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.99/1.22  thf('113', plain,
% 0.99/1.22      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.99/1.22      inference('sup-', [status(thm)], ['111', '112'])).
% 0.99/1.22  thf('114', plain,
% 0.99/1.22      (![X22 : $i, X23 : $i]:
% 0.99/1.22         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 0.99/1.22           = (k2_xboole_0 @ X22 @ X23))),
% 0.99/1.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.99/1.22  thf('115', plain,
% 0.99/1.22      (((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.99/1.22         = (k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_B))),
% 0.99/1.22      inference('sup+', [status(thm)], ['113', '114'])).
% 0.99/1.22  thf('116', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.22  thf('117', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['9', '10'])).
% 0.99/1.22  thf('118', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.22  thf('119', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['67', '68'])).
% 0.99/1.22  thf(t49_xboole_1, axiom,
% 0.99/1.22    (![A:$i,B:$i,C:$i]:
% 0.99/1.22     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.99/1.22       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.99/1.22  thf('120', plain,
% 0.99/1.22      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.99/1.22         ((k3_xboole_0 @ X33 @ (k4_xboole_0 @ X34 @ X35))
% 0.99/1.22           = (k4_xboole_0 @ (k3_xboole_0 @ X33 @ X34) @ X35))),
% 0.99/1.22      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.99/1.22  thf('121', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]:
% 0.99/1.22         ((k3_xboole_0 @ X1 @ k1_xboole_0)
% 0.99/1.22           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['119', '120'])).
% 0.99/1.22  thf(t2_boole, axiom,
% 0.99/1.22    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.99/1.22  thf('122', plain,
% 0.99/1.22      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.99/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 0.99/1.22  thf('123', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]:
% 0.99/1.22         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.99/1.22      inference('demod', [status(thm)], ['121', '122'])).
% 0.99/1.22  thf('124', plain,
% 0.99/1.22      (![X22 : $i, X23 : $i]:
% 0.99/1.22         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 0.99/1.22           = (k2_xboole_0 @ X22 @ X23))),
% 0.99/1.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.99/1.22  thf('125', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]:
% 0.99/1.22         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.99/1.22           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.99/1.22      inference('sup+', [status(thm)], ['123', '124'])).
% 0.99/1.22  thf('126', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.99/1.22      inference('cnf', [status(esa)], [t1_boole])).
% 0.99/1.22  thf('127', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]:
% 0.99/1.22         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.99/1.22      inference('demod', [status(thm)], ['125', '126'])).
% 0.99/1.22  thf('128', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.99/1.22      inference('demod', [status(thm)], ['115', '116', '117', '118', '127'])).
% 0.99/1.22  thf('129', plain,
% 0.99/1.22      (((((k1_xboole_0) != (k1_xboole_0))
% 0.99/1.22         | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_C @ sk_B))))
% 0.99/1.22         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('demod', [status(thm)], ['97', '128'])).
% 0.99/1.22  thf('130', plain,
% 0.99/1.22      (((r1_tarski @ sk_B @ (k3_xboole_0 @ sk_C @ sk_B)))
% 0.99/1.22         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('simplify', [status(thm)], ['129'])).
% 0.99/1.22  thf('131', plain,
% 0.99/1.22      (![X3 : $i, X5 : $i]:
% 0.99/1.22         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.99/1.22      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.99/1.22  thf('132', plain,
% 0.99/1.22      ((((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ sk_B)) = (k1_xboole_0)))
% 0.99/1.22         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('sup-', [status(thm)], ['130', '131'])).
% 0.99/1.22  thf('133', plain,
% 0.99/1.22      (![X22 : $i, X23 : $i]:
% 0.99/1.22         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 0.99/1.22           = (k2_xboole_0 @ X22 @ X23))),
% 0.99/1.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.99/1.22  thf('134', plain,
% 0.99/1.22      ((((k2_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_B) @ k1_xboole_0)
% 0.99/1.22          = (k2_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_B)))
% 0.99/1.22         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('sup+', [status(thm)], ['132', '133'])).
% 0.99/1.22  thf('135', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.22  thf('136', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.22      inference('sup+', [status(thm)], ['9', '10'])).
% 0.99/1.22  thf('137', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.22  thf('138', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]:
% 0.99/1.22         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.99/1.22      inference('demod', [status(thm)], ['125', '126'])).
% 0.99/1.22  thf('139', plain,
% 0.99/1.22      ((((k3_xboole_0 @ sk_C @ sk_B) = (sk_B)))
% 0.99/1.22         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 0.99/1.22  thf('140', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.99/1.22      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.99/1.22  thf(t29_xboole_1, axiom,
% 0.99/1.22    (![A:$i,B:$i,C:$i]:
% 0.99/1.22     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 0.99/1.22  thf('141', plain,
% 0.99/1.22      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.99/1.22         (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ (k2_xboole_0 @ X10 @ X12))),
% 0.99/1.22      inference('cnf', [status(esa)], [t29_xboole_1])).
% 0.99/1.22  thf('142', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.99/1.22      inference('sup+', [status(thm)], ['140', '141'])).
% 0.99/1.22  thf('143', plain,
% 0.99/1.22      (((r1_tarski @ sk_B @ sk_C))
% 0.99/1.22         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.99/1.22               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('sup+', [status(thm)], ['139', '142'])).
% 0.99/1.22  thf('144', plain,
% 0.99/1.22      ((~ (r1_tarski @ sk_B @ sk_C)) <= (~ ((r1_tarski @ sk_B @ sk_C)))),
% 0.99/1.22      inference('split', [status(esa)], ['0'])).
% 0.99/1.22  thf('145', plain,
% 0.99/1.22      (~
% 0.99/1.22       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.99/1.22       ((r1_tarski @ sk_B @ sk_C))),
% 0.99/1.22      inference('sup-', [status(thm)], ['143', '144'])).
% 0.99/1.22  thf('146', plain, ($false),
% 0.99/1.22      inference('sat_resolution*', [status(thm)], ['1', '34', '35', '145'])).
% 0.99/1.22  
% 0.99/1.22  % SZS output end Refutation
% 0.99/1.22  
% 0.99/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
