%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9RWAdYvvRM

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:09 EST 2020

% Result     : Theorem 11.64s
% Output     : Refutation 11.64s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 463 expanded)
%              Number of leaves         :   30 ( 146 expanded)
%              Depth                    :   17
%              Number of atoms          :  917 (4102 expanded)
%              Number of equality atoms :   45 ( 166 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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

thf('2',plain,(
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

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ X30 )
      | ( r2_hidden @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X34: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( r1_tarski @ X27 @ X25 )
      | ( X26
       != ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_tarski @ X27 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ X30 )
      | ( r2_hidden @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X34: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('24',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_tarski @ X27 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('26',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('33',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','19','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('38',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('41',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('45',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['37','45'])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ X0 @ sk_C_1 )
      | ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('53',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('54',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ X0 @ sk_C_1 )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( r1_tarski @ sk_B @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','55'])).

thf('57',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('58',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['36','60'])).

thf('62',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['35','61'])).

thf('63',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['38'])).

thf('64',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('66',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('67',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['63','74'])).

thf('76',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('77',plain,
    ( ( r1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['38'])).

thf('79',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['36','60','78'])).

thf('80',plain,(
    r1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['77','79'])).

thf('81',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('82',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('83',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('85',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('86',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['83','86'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('89',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,
    ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['80','91'])).

thf('93',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('94',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('95',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['92','95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['62','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9RWAdYvvRM
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 11.64/11.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.64/11.84  % Solved by: fo/fo7.sh
% 11.64/11.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.64/11.84  % done 10452 iterations in 11.383s
% 11.64/11.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.64/11.84  % SZS output start Refutation
% 11.64/11.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 11.64/11.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 11.64/11.84  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 11.64/11.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.64/11.84  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 11.64/11.84  thf(sk_A_type, type, sk_A: $i).
% 11.64/11.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 11.64/11.84  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 11.64/11.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 11.64/11.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.64/11.84  thf(sk_B_type, type, sk_B: $i).
% 11.64/11.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.64/11.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.64/11.84  thf(sk_C_1_type, type, sk_C_1: $i).
% 11.64/11.84  thf(t31_subset_1, conjecture,
% 11.64/11.84    (![A:$i,B:$i]:
% 11.64/11.84     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 11.64/11.84       ( ![C:$i]:
% 11.64/11.84         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 11.64/11.84           ( ( r1_tarski @ B @ C ) <=>
% 11.64/11.84             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 11.64/11.84  thf(zf_stmt_0, negated_conjecture,
% 11.64/11.84    (~( ![A:$i,B:$i]:
% 11.64/11.84        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 11.64/11.84          ( ![C:$i]:
% 11.64/11.84            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 11.64/11.84              ( ( r1_tarski @ B @ C ) <=>
% 11.64/11.84                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 11.64/11.84    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 11.64/11.84  thf('0', plain,
% 11.64/11.84      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 11.64/11.84           (k3_subset_1 @ sk_A @ sk_B))
% 11.64/11.84        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 11.64/11.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.64/11.84  thf('1', plain,
% 11.64/11.84      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 11.64/11.84           (k3_subset_1 @ sk_A @ sk_B)))
% 11.64/11.84         <= (~
% 11.64/11.84             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 11.64/11.84               (k3_subset_1 @ sk_A @ sk_B))))),
% 11.64/11.84      inference('split', [status(esa)], ['0'])).
% 11.64/11.84  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 11.64/11.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.64/11.84  thf(d2_subset_1, axiom,
% 11.64/11.84    (![A:$i,B:$i]:
% 11.64/11.84     ( ( ( v1_xboole_0 @ A ) =>
% 11.64/11.84         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 11.64/11.84       ( ( ~( v1_xboole_0 @ A ) ) =>
% 11.64/11.84         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 11.64/11.84  thf('3', plain,
% 11.64/11.84      (![X29 : $i, X30 : $i]:
% 11.64/11.84         (~ (m1_subset_1 @ X29 @ X30)
% 11.64/11.84          | (r2_hidden @ X29 @ X30)
% 11.64/11.84          | (v1_xboole_0 @ X30))),
% 11.64/11.84      inference('cnf', [status(esa)], [d2_subset_1])).
% 11.64/11.84  thf('4', plain,
% 11.64/11.84      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 11.64/11.84        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 11.64/11.84      inference('sup-', [status(thm)], ['2', '3'])).
% 11.64/11.84  thf(fc1_subset_1, axiom,
% 11.64/11.84    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 11.64/11.84  thf('5', plain, (![X34 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X34))),
% 11.64/11.84      inference('cnf', [status(esa)], [fc1_subset_1])).
% 11.64/11.84  thf('6', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 11.64/11.84      inference('clc', [status(thm)], ['4', '5'])).
% 11.64/11.84  thf(d1_zfmisc_1, axiom,
% 11.64/11.84    (![A:$i,B:$i]:
% 11.64/11.84     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 11.64/11.84       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 11.64/11.84  thf('7', plain,
% 11.64/11.84      (![X25 : $i, X26 : $i, X27 : $i]:
% 11.64/11.84         (~ (r2_hidden @ X27 @ X26)
% 11.64/11.84          | (r1_tarski @ X27 @ X25)
% 11.64/11.84          | ((X26) != (k1_zfmisc_1 @ X25)))),
% 11.64/11.84      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 11.64/11.84  thf('8', plain,
% 11.64/11.84      (![X25 : $i, X27 : $i]:
% 11.64/11.84         ((r1_tarski @ X27 @ X25) | ~ (r2_hidden @ X27 @ (k1_zfmisc_1 @ X25)))),
% 11.64/11.84      inference('simplify', [status(thm)], ['7'])).
% 11.64/11.84  thf('9', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 11.64/11.84      inference('sup-', [status(thm)], ['6', '8'])).
% 11.64/11.84  thf(t28_xboole_1, axiom,
% 11.64/11.84    (![A:$i,B:$i]:
% 11.64/11.84     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 11.64/11.84  thf('10', plain,
% 11.64/11.84      (![X13 : $i, X14 : $i]:
% 11.64/11.84         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 11.64/11.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 11.64/11.84  thf('11', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 11.64/11.84      inference('sup-', [status(thm)], ['9', '10'])).
% 11.64/11.84  thf(commutativity_k3_xboole_0, axiom,
% 11.64/11.84    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 11.64/11.84  thf('12', plain,
% 11.64/11.84      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 11.64/11.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.64/11.84  thf(t100_xboole_1, axiom,
% 11.64/11.84    (![A:$i,B:$i]:
% 11.64/11.84     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 11.64/11.84  thf('13', plain,
% 11.64/11.84      (![X6 : $i, X7 : $i]:
% 11.64/11.84         ((k4_xboole_0 @ X6 @ X7)
% 11.64/11.84           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 11.64/11.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 11.64/11.84  thf('14', plain,
% 11.64/11.84      (![X0 : $i, X1 : $i]:
% 11.64/11.84         ((k4_xboole_0 @ X0 @ X1)
% 11.64/11.84           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 11.64/11.84      inference('sup+', [status(thm)], ['12', '13'])).
% 11.64/11.84  thf('15', plain,
% 11.64/11.84      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 11.64/11.84      inference('sup+', [status(thm)], ['11', '14'])).
% 11.64/11.84  thf('16', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 11.64/11.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.64/11.84  thf(d5_subset_1, axiom,
% 11.64/11.84    (![A:$i,B:$i]:
% 11.64/11.84     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 11.64/11.84       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 11.64/11.84  thf('17', plain,
% 11.64/11.84      (![X32 : $i, X33 : $i]:
% 11.64/11.84         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 11.64/11.84          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 11.64/11.84      inference('cnf', [status(esa)], [d5_subset_1])).
% 11.64/11.84  thf('18', plain,
% 11.64/11.84      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 11.64/11.84      inference('sup-', [status(thm)], ['16', '17'])).
% 11.64/11.84  thf('19', plain,
% 11.64/11.84      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 11.64/11.84      inference('sup+', [status(thm)], ['15', '18'])).
% 11.64/11.84  thf('20', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 11.64/11.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.64/11.84  thf('21', plain,
% 11.64/11.84      (![X29 : $i, X30 : $i]:
% 11.64/11.84         (~ (m1_subset_1 @ X29 @ X30)
% 11.64/11.84          | (r2_hidden @ X29 @ X30)
% 11.64/11.84          | (v1_xboole_0 @ X30))),
% 11.64/11.84      inference('cnf', [status(esa)], [d2_subset_1])).
% 11.64/11.84  thf('22', plain,
% 11.64/11.84      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 11.64/11.84        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 11.64/11.84      inference('sup-', [status(thm)], ['20', '21'])).
% 11.64/11.84  thf('23', plain, (![X34 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X34))),
% 11.64/11.84      inference('cnf', [status(esa)], [fc1_subset_1])).
% 11.64/11.84  thf('24', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 11.64/11.84      inference('clc', [status(thm)], ['22', '23'])).
% 11.64/11.84  thf('25', plain,
% 11.64/11.84      (![X25 : $i, X27 : $i]:
% 11.64/11.84         ((r1_tarski @ X27 @ X25) | ~ (r2_hidden @ X27 @ (k1_zfmisc_1 @ X25)))),
% 11.64/11.84      inference('simplify', [status(thm)], ['7'])).
% 11.64/11.84  thf('26', plain, ((r1_tarski @ sk_B @ sk_A)),
% 11.64/11.84      inference('sup-', [status(thm)], ['24', '25'])).
% 11.64/11.84  thf('27', plain,
% 11.64/11.84      (![X13 : $i, X14 : $i]:
% 11.64/11.84         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 11.64/11.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 11.64/11.84  thf('28', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 11.64/11.84      inference('sup-', [status(thm)], ['26', '27'])).
% 11.64/11.84  thf('29', plain,
% 11.64/11.84      (![X0 : $i, X1 : $i]:
% 11.64/11.84         ((k4_xboole_0 @ X0 @ X1)
% 11.64/11.84           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 11.64/11.84      inference('sup+', [status(thm)], ['12', '13'])).
% 11.64/11.84  thf('30', plain,
% 11.64/11.84      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 11.64/11.84      inference('sup+', [status(thm)], ['28', '29'])).
% 11.64/11.84  thf('31', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 11.64/11.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.64/11.84  thf('32', plain,
% 11.64/11.84      (![X32 : $i, X33 : $i]:
% 11.64/11.84         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 11.64/11.84          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 11.64/11.84      inference('cnf', [status(esa)], [d5_subset_1])).
% 11.64/11.84  thf('33', plain,
% 11.64/11.84      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 11.64/11.84      inference('sup-', [status(thm)], ['31', '32'])).
% 11.64/11.84  thf('34', plain,
% 11.64/11.84      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 11.64/11.84      inference('sup+', [status(thm)], ['30', '33'])).
% 11.64/11.84  thf('35', plain,
% 11.64/11.84      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 11.64/11.84           (k5_xboole_0 @ sk_A @ sk_B)))
% 11.64/11.84         <= (~
% 11.64/11.84             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 11.64/11.84               (k3_subset_1 @ sk_A @ sk_B))))),
% 11.64/11.84      inference('demod', [status(thm)], ['1', '19', '34'])).
% 11.64/11.84  thf('36', plain,
% 11.64/11.84      (~
% 11.64/11.84       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 11.64/11.84         (k3_subset_1 @ sk_A @ sk_B))) | 
% 11.64/11.84       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 11.64/11.84      inference('split', [status(esa)], ['0'])).
% 11.64/11.84  thf('37', plain,
% 11.64/11.84      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 11.64/11.84      inference('sup+', [status(thm)], ['15', '18'])).
% 11.64/11.84  thf('38', plain,
% 11.64/11.84      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 11.64/11.84         (k3_subset_1 @ sk_A @ sk_B))
% 11.64/11.84        | (r1_tarski @ sk_B @ sk_C_1))),
% 11.64/11.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.64/11.84  thf('39', plain,
% 11.64/11.84      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 11.64/11.84         (k3_subset_1 @ sk_A @ sk_B)))
% 11.64/11.84         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 11.64/11.84               (k3_subset_1 @ sk_A @ sk_B))))),
% 11.64/11.84      inference('split', [status(esa)], ['38'])).
% 11.64/11.84  thf('40', plain,
% 11.64/11.84      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 11.64/11.84      inference('sup-', [status(thm)], ['31', '32'])).
% 11.64/11.84  thf(t106_xboole_1, axiom,
% 11.64/11.84    (![A:$i,B:$i,C:$i]:
% 11.64/11.84     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 11.64/11.84       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 11.64/11.84  thf('41', plain,
% 11.64/11.84      (![X8 : $i, X9 : $i, X10 : $i]:
% 11.64/11.84         ((r1_xboole_0 @ X8 @ X10)
% 11.64/11.84          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 11.64/11.84      inference('cnf', [status(esa)], [t106_xboole_1])).
% 11.64/11.84  thf('42', plain,
% 11.64/11.84      (![X0 : $i]:
% 11.64/11.84         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 11.64/11.84          | (r1_xboole_0 @ X0 @ sk_B))),
% 11.64/11.84      inference('sup-', [status(thm)], ['40', '41'])).
% 11.64/11.84  thf('43', plain,
% 11.64/11.84      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))
% 11.64/11.84         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 11.64/11.84               (k3_subset_1 @ sk_A @ sk_B))))),
% 11.64/11.84      inference('sup-', [status(thm)], ['39', '42'])).
% 11.64/11.84  thf(symmetry_r1_xboole_0, axiom,
% 11.64/11.84    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 11.64/11.84  thf('44', plain,
% 11.64/11.84      (![X4 : $i, X5 : $i]:
% 11.64/11.84         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 11.64/11.84      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 11.64/11.84  thf('45', plain,
% 11.64/11.84      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 11.64/11.84         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 11.64/11.84               (k3_subset_1 @ sk_A @ sk_B))))),
% 11.64/11.84      inference('sup-', [status(thm)], ['43', '44'])).
% 11.64/11.84  thf('46', plain,
% 11.64/11.84      (((r1_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)))
% 11.64/11.84         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 11.64/11.84               (k3_subset_1 @ sk_A @ sk_B))))),
% 11.64/11.84      inference('sup+', [status(thm)], ['37', '45'])).
% 11.64/11.84  thf('47', plain,
% 11.64/11.84      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 11.64/11.84      inference('sup+', [status(thm)], ['11', '14'])).
% 11.64/11.84  thf(t39_xboole_1, axiom,
% 11.64/11.84    (![A:$i,B:$i]:
% 11.64/11.84     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 11.64/11.84  thf('48', plain,
% 11.64/11.84      (![X17 : $i, X18 : $i]:
% 11.64/11.84         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 11.64/11.84           = (k2_xboole_0 @ X17 @ X18))),
% 11.64/11.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 11.64/11.84  thf(t73_xboole_1, axiom,
% 11.64/11.84    (![A:$i,B:$i,C:$i]:
% 11.64/11.84     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 11.64/11.84       ( r1_tarski @ A @ B ) ))).
% 11.64/11.84  thf('49', plain,
% 11.64/11.84      (![X21 : $i, X22 : $i, X23 : $i]:
% 11.64/11.84         ((r1_tarski @ X21 @ X22)
% 11.64/11.84          | ~ (r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 11.64/11.84          | ~ (r1_xboole_0 @ X21 @ X23))),
% 11.64/11.84      inference('cnf', [status(esa)], [t73_xboole_1])).
% 11.64/11.84  thf('50', plain,
% 11.64/11.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.64/11.84         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 11.64/11.84          | ~ (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 11.64/11.84          | (r1_tarski @ X2 @ X1))),
% 11.64/11.84      inference('sup-', [status(thm)], ['48', '49'])).
% 11.64/11.84  thf('51', plain,
% 11.64/11.84      (![X0 : $i]:
% 11.64/11.84         (~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 11.64/11.84          | (r1_tarski @ X0 @ sk_C_1)
% 11.64/11.84          | ~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_C_1 @ sk_A)))),
% 11.64/11.84      inference('sup-', [status(thm)], ['47', '50'])).
% 11.64/11.84  thf('52', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 11.64/11.84      inference('sup-', [status(thm)], ['6', '8'])).
% 11.64/11.84  thf(t12_xboole_1, axiom,
% 11.64/11.84    (![A:$i,B:$i]:
% 11.64/11.84     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 11.64/11.84  thf('53', plain,
% 11.64/11.84      (![X11 : $i, X12 : $i]:
% 11.64/11.84         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 11.64/11.84      inference('cnf', [status(esa)], [t12_xboole_1])).
% 11.64/11.84  thf('54', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 11.64/11.84      inference('sup-', [status(thm)], ['52', '53'])).
% 11.64/11.84  thf('55', plain,
% 11.64/11.84      (![X0 : $i]:
% 11.64/11.84         (~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 11.64/11.84          | (r1_tarski @ X0 @ sk_C_1)
% 11.64/11.84          | ~ (r1_tarski @ X0 @ sk_A))),
% 11.64/11.84      inference('demod', [status(thm)], ['51', '54'])).
% 11.64/11.84  thf('56', plain,
% 11.64/11.84      (((~ (r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_C_1)))
% 11.64/11.84         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 11.64/11.84               (k3_subset_1 @ sk_A @ sk_B))))),
% 11.64/11.84      inference('sup-', [status(thm)], ['46', '55'])).
% 11.64/11.84  thf('57', plain, ((r1_tarski @ sk_B @ sk_A)),
% 11.64/11.84      inference('sup-', [status(thm)], ['24', '25'])).
% 11.64/11.84  thf('58', plain,
% 11.64/11.84      (((r1_tarski @ sk_B @ sk_C_1))
% 11.64/11.84         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 11.64/11.84               (k3_subset_1 @ sk_A @ sk_B))))),
% 11.64/11.84      inference('demod', [status(thm)], ['56', '57'])).
% 11.64/11.84  thf('59', plain,
% 11.64/11.84      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 11.64/11.84      inference('split', [status(esa)], ['0'])).
% 11.64/11.84  thf('60', plain,
% 11.64/11.84      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 11.64/11.84       ~
% 11.64/11.84       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 11.64/11.84         (k3_subset_1 @ sk_A @ sk_B)))),
% 11.64/11.84      inference('sup-', [status(thm)], ['58', '59'])).
% 11.64/11.84  thf('61', plain,
% 11.64/11.84      (~
% 11.64/11.84       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 11.64/11.84         (k3_subset_1 @ sk_A @ sk_B)))),
% 11.64/11.84      inference('sat_resolution*', [status(thm)], ['36', '60'])).
% 11.64/11.84  thf('62', plain,
% 11.64/11.84      (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 11.64/11.84          (k5_xboole_0 @ sk_A @ sk_B))),
% 11.64/11.84      inference('simpl_trail', [status(thm)], ['35', '61'])).
% 11.64/11.84  thf('63', plain,
% 11.64/11.84      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 11.64/11.84      inference('split', [status(esa)], ['38'])).
% 11.64/11.84  thf('64', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 11.64/11.84      inference('sup-', [status(thm)], ['9', '10'])).
% 11.64/11.84  thf('65', plain,
% 11.64/11.84      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 11.64/11.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.64/11.84  thf(t48_xboole_1, axiom,
% 11.64/11.84    (![A:$i,B:$i]:
% 11.64/11.84     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 11.64/11.84  thf('66', plain,
% 11.64/11.84      (![X19 : $i, X20 : $i]:
% 11.64/11.84         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 11.64/11.84           = (k3_xboole_0 @ X19 @ X20))),
% 11.64/11.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.64/11.84  thf('67', plain,
% 11.64/11.84      (![X8 : $i, X9 : $i, X10 : $i]:
% 11.64/11.84         ((r1_xboole_0 @ X8 @ X10)
% 11.64/11.84          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 11.64/11.84      inference('cnf', [status(esa)], [t106_xboole_1])).
% 11.64/11.84  thf('68', plain,
% 11.64/11.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.64/11.84         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 11.64/11.84          | (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 11.64/11.84      inference('sup-', [status(thm)], ['66', '67'])).
% 11.64/11.84  thf('69', plain,
% 11.64/11.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.64/11.84         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 11.64/11.84          | (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 11.64/11.84      inference('sup-', [status(thm)], ['65', '68'])).
% 11.64/11.84  thf('70', plain,
% 11.64/11.84      (![X0 : $i]:
% 11.64/11.84         (~ (r1_tarski @ X0 @ sk_C_1)
% 11.64/11.84          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_C_1)))),
% 11.64/11.84      inference('sup-', [status(thm)], ['64', '69'])).
% 11.64/11.84  thf('71', plain,
% 11.64/11.84      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 11.64/11.84      inference('sup-', [status(thm)], ['16', '17'])).
% 11.64/11.84  thf('72', plain,
% 11.64/11.84      (![X0 : $i]:
% 11.64/11.84         (~ (r1_tarski @ X0 @ sk_C_1)
% 11.64/11.84          | (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 11.64/11.84      inference('demod', [status(thm)], ['70', '71'])).
% 11.64/11.84  thf('73', plain,
% 11.64/11.84      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 11.64/11.84      inference('sup+', [status(thm)], ['15', '18'])).
% 11.64/11.84  thf('74', plain,
% 11.64/11.84      (![X0 : $i]:
% 11.64/11.84         (~ (r1_tarski @ X0 @ sk_C_1)
% 11.64/11.84          | (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 11.64/11.84      inference('demod', [status(thm)], ['72', '73'])).
% 11.64/11.84  thf('75', plain,
% 11.64/11.84      (((r1_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)))
% 11.64/11.84         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 11.64/11.84      inference('sup-', [status(thm)], ['63', '74'])).
% 11.64/11.84  thf('76', plain,
% 11.64/11.84      (![X4 : $i, X5 : $i]:
% 11.64/11.84         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 11.64/11.84      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 11.64/11.84  thf('77', plain,
% 11.64/11.84      (((r1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B))
% 11.64/11.84         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 11.64/11.84      inference('sup-', [status(thm)], ['75', '76'])).
% 11.64/11.84  thf('78', plain,
% 11.64/11.84      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 11.64/11.84       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 11.64/11.84         (k3_subset_1 @ sk_A @ sk_B)))),
% 11.64/11.84      inference('split', [status(esa)], ['38'])).
% 11.64/11.84  thf('79', plain, (((r1_tarski @ sk_B @ sk_C_1))),
% 11.64/11.84      inference('sat_resolution*', [status(thm)], ['36', '60', '78'])).
% 11.64/11.84  thf('80', plain, ((r1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 11.64/11.84      inference('simpl_trail', [status(thm)], ['77', '79'])).
% 11.64/11.84  thf('81', plain,
% 11.64/11.84      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 11.64/11.84      inference('sup+', [status(thm)], ['28', '29'])).
% 11.64/11.84  thf('82', plain,
% 11.64/11.84      (![X17 : $i, X18 : $i]:
% 11.64/11.84         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 11.64/11.84           = (k2_xboole_0 @ X17 @ X18))),
% 11.64/11.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 11.64/11.84  thf('83', plain,
% 11.64/11.84      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))
% 11.64/11.84         = (k2_xboole_0 @ sk_B @ sk_A))),
% 11.64/11.84      inference('sup+', [status(thm)], ['81', '82'])).
% 11.64/11.84  thf('84', plain, ((r1_tarski @ sk_B @ sk_A)),
% 11.64/11.84      inference('sup-', [status(thm)], ['24', '25'])).
% 11.64/11.84  thf('85', plain,
% 11.64/11.84      (![X11 : $i, X12 : $i]:
% 11.64/11.84         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 11.64/11.84      inference('cnf', [status(esa)], [t12_xboole_1])).
% 11.64/11.84  thf('86', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 11.64/11.84      inference('sup-', [status(thm)], ['84', '85'])).
% 11.64/11.84  thf('87', plain,
% 11.64/11.84      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 11.64/11.84      inference('demod', [status(thm)], ['83', '86'])).
% 11.64/11.84  thf(commutativity_k2_xboole_0, axiom,
% 11.64/11.84    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 11.64/11.84  thf('88', plain,
% 11.64/11.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 11.64/11.84      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 11.64/11.84  thf('89', plain,
% 11.64/11.84      (![X21 : $i, X22 : $i, X23 : $i]:
% 11.64/11.84         ((r1_tarski @ X21 @ X22)
% 11.64/11.84          | ~ (r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 11.64/11.84          | ~ (r1_xboole_0 @ X21 @ X23))),
% 11.64/11.84      inference('cnf', [status(esa)], [t73_xboole_1])).
% 11.64/11.84  thf('90', plain,
% 11.64/11.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.64/11.84         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 11.64/11.84          | ~ (r1_xboole_0 @ X2 @ X1)
% 11.64/11.84          | (r1_tarski @ X2 @ X0))),
% 11.64/11.84      inference('sup-', [status(thm)], ['88', '89'])).
% 11.64/11.84  thf('91', plain,
% 11.64/11.84      (![X0 : $i]:
% 11.64/11.84         (~ (r1_tarski @ X0 @ sk_A)
% 11.64/11.84          | (r1_tarski @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))
% 11.64/11.84          | ~ (r1_xboole_0 @ X0 @ sk_B))),
% 11.64/11.84      inference('sup-', [status(thm)], ['87', '90'])).
% 11.64/11.84  thf('92', plain,
% 11.64/11.84      (((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 11.64/11.84         (k5_xboole_0 @ sk_A @ sk_B))
% 11.64/11.84        | ~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_A))),
% 11.64/11.84      inference('sup-', [status(thm)], ['80', '91'])).
% 11.64/11.84  thf('93', plain,
% 11.64/11.84      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 11.64/11.84      inference('sup+', [status(thm)], ['11', '14'])).
% 11.64/11.84  thf(t36_xboole_1, axiom,
% 11.64/11.84    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 11.64/11.84  thf('94', plain,
% 11.64/11.84      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 11.64/11.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 11.64/11.84  thf('95', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_A)),
% 11.64/11.84      inference('sup+', [status(thm)], ['93', '94'])).
% 11.64/11.84  thf('96', plain,
% 11.64/11.84      ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ (k5_xboole_0 @ sk_A @ sk_B))),
% 11.64/11.84      inference('demod', [status(thm)], ['92', '95'])).
% 11.64/11.84  thf('97', plain, ($false), inference('demod', [status(thm)], ['62', '96'])).
% 11.64/11.84  
% 11.64/11.84  % SZS output end Refutation
% 11.64/11.84  
% 11.64/11.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
