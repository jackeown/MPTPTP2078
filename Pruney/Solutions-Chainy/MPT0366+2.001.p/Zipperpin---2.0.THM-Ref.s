%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GqpSuSPZtD

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:07 EST 2020

% Result     : Theorem 2.52s
% Output     : Refutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 173 expanded)
%              Number of leaves         :   34 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  694 (1416 expanded)
%              Number of equality atoms :   58 (  85 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t47_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( r1_xboole_0 @ D @ C ) )
               => ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( ( r1_tarski @ B @ C )
                    & ( r1_xboole_0 @ D @ C ) )
                 => ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ X32 )
      | ( r2_hidden @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X36: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( r1_tarski @ X29 @ X27 )
      | ( X28
       != ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ X29 @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_A )
    = sk_D ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k5_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_D )
    = ( k5_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ~ ( r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','18'])).

thf('20',plain,(
    r1_xboole_0 @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('22',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k5_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_D ) @ ( k3_xboole_0 @ sk_A @ sk_D ) )
    = sk_A ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_A )
    = sk_D ),
    inference('sup-',[status(thm)],['8','9'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k5_xboole_0 @ sk_A @ sk_D ) )
    = sk_A ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) )
      | ~ ( r1_xboole_0 @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( k5_xboole_0 @ sk_A @ sk_D ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_D ) )
    | ~ ( r1_tarski @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ X32 )
      | ( r2_hidden @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X36: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('41',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ X29 @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('43',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_D ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('49',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_D ) )
    = sk_B ),
    inference(demod,[status(thm)],['52','53'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('55',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('56',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('60',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('61',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('64',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('66',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','67'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('69',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['54','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['19','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GqpSuSPZtD
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:04:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.52/2.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.52/2.71  % Solved by: fo/fo7.sh
% 2.52/2.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.52/2.71  % done 1845 iterations in 2.244s
% 2.52/2.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.52/2.71  % SZS output start Refutation
% 2.52/2.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.52/2.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.52/2.71  thf(sk_A_type, type, sk_A: $i).
% 2.52/2.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.52/2.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.52/2.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.52/2.71  thf(sk_B_type, type, sk_B: $i).
% 2.52/2.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.52/2.71  thf(sk_D_type, type, sk_D: $i).
% 2.52/2.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.52/2.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.52/2.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.52/2.71  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.52/2.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.52/2.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.52/2.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.52/2.71  thf(t47_subset_1, conjecture,
% 2.52/2.71    (![A:$i,B:$i]:
% 2.52/2.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.52/2.71       ( ![C:$i]:
% 2.52/2.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.52/2.71           ( ![D:$i]:
% 2.52/2.71             ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 2.52/2.71               ( ( ( r1_tarski @ B @ C ) & ( r1_xboole_0 @ D @ C ) ) =>
% 2.52/2.71                 ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) ) ))).
% 2.52/2.71  thf(zf_stmt_0, negated_conjecture,
% 2.52/2.71    (~( ![A:$i,B:$i]:
% 2.52/2.71        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.52/2.71          ( ![C:$i]:
% 2.52/2.71            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.52/2.71              ( ![D:$i]:
% 2.52/2.71                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 2.52/2.71                  ( ( ( r1_tarski @ B @ C ) & ( r1_xboole_0 @ D @ C ) ) =>
% 2.52/2.71                    ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) ) ) )),
% 2.52/2.71    inference('cnf.neg', [status(esa)], [t47_subset_1])).
% 2.52/2.71  thf('0', plain, (~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_D))),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf(d2_subset_1, axiom,
% 2.52/2.71    (![A:$i,B:$i]:
% 2.52/2.71     ( ( ( v1_xboole_0 @ A ) =>
% 2.52/2.71         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 2.52/2.71       ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.52/2.71         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 2.52/2.71  thf('2', plain,
% 2.52/2.71      (![X31 : $i, X32 : $i]:
% 2.52/2.71         (~ (m1_subset_1 @ X31 @ X32)
% 2.52/2.71          | (r2_hidden @ X31 @ X32)
% 2.52/2.71          | (v1_xboole_0 @ X32))),
% 2.52/2.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.52/2.71  thf('3', plain,
% 2.52/2.71      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 2.52/2.71        | (r2_hidden @ sk_D @ (k1_zfmisc_1 @ sk_A)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['1', '2'])).
% 2.52/2.71  thf(fc1_subset_1, axiom,
% 2.52/2.71    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.52/2.71  thf('4', plain, (![X36 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 2.52/2.71      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.52/2.71  thf('5', plain, ((r2_hidden @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 2.52/2.71      inference('clc', [status(thm)], ['3', '4'])).
% 2.52/2.71  thf(d1_zfmisc_1, axiom,
% 2.52/2.71    (![A:$i,B:$i]:
% 2.52/2.71     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 2.52/2.71       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 2.52/2.71  thf('6', plain,
% 2.52/2.71      (![X27 : $i, X28 : $i, X29 : $i]:
% 2.52/2.71         (~ (r2_hidden @ X29 @ X28)
% 2.52/2.71          | (r1_tarski @ X29 @ X27)
% 2.52/2.71          | ((X28) != (k1_zfmisc_1 @ X27)))),
% 2.52/2.71      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 2.52/2.71  thf('7', plain,
% 2.52/2.71      (![X27 : $i, X29 : $i]:
% 2.52/2.71         ((r1_tarski @ X29 @ X27) | ~ (r2_hidden @ X29 @ (k1_zfmisc_1 @ X27)))),
% 2.52/2.71      inference('simplify', [status(thm)], ['6'])).
% 2.52/2.71  thf('8', plain, ((r1_tarski @ sk_D @ sk_A)),
% 2.52/2.71      inference('sup-', [status(thm)], ['5', '7'])).
% 2.52/2.71  thf(t28_xboole_1, axiom,
% 2.52/2.71    (![A:$i,B:$i]:
% 2.52/2.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.52/2.71  thf('9', plain,
% 2.52/2.71      (![X15 : $i, X16 : $i]:
% 2.52/2.71         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 2.52/2.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.52/2.71  thf('10', plain, (((k3_xboole_0 @ sk_D @ sk_A) = (sk_D))),
% 2.52/2.71      inference('sup-', [status(thm)], ['8', '9'])).
% 2.52/2.71  thf(commutativity_k3_xboole_0, axiom,
% 2.52/2.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.52/2.71  thf('11', plain,
% 2.52/2.71      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.52/2.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.52/2.71  thf(t100_xboole_1, axiom,
% 2.52/2.71    (![A:$i,B:$i]:
% 2.52/2.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.52/2.71  thf('12', plain,
% 2.52/2.71      (![X10 : $i, X11 : $i]:
% 2.52/2.71         ((k4_xboole_0 @ X10 @ X11)
% 2.52/2.71           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 2.52/2.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.52/2.71  thf('13', plain,
% 2.52/2.71      (![X0 : $i, X1 : $i]:
% 2.52/2.71         ((k4_xboole_0 @ X0 @ X1)
% 2.52/2.71           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.52/2.71      inference('sup+', [status(thm)], ['11', '12'])).
% 2.52/2.71  thf('14', plain,
% 2.52/2.71      (((k4_xboole_0 @ sk_A @ sk_D) = (k5_xboole_0 @ sk_A @ sk_D))),
% 2.52/2.71      inference('sup+', [status(thm)], ['10', '13'])).
% 2.52/2.71  thf('15', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf(d5_subset_1, axiom,
% 2.52/2.71    (![A:$i,B:$i]:
% 2.52/2.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.52/2.71       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.52/2.71  thf('16', plain,
% 2.52/2.71      (![X34 : $i, X35 : $i]:
% 2.52/2.71         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 2.52/2.71          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 2.52/2.71      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.52/2.71  thf('17', plain,
% 2.52/2.71      (((k3_subset_1 @ sk_A @ sk_D) = (k4_xboole_0 @ sk_A @ sk_D))),
% 2.52/2.71      inference('sup-', [status(thm)], ['15', '16'])).
% 2.52/2.71  thf('18', plain,
% 2.52/2.71      (((k3_subset_1 @ sk_A @ sk_D) = (k5_xboole_0 @ sk_A @ sk_D))),
% 2.52/2.71      inference('sup+', [status(thm)], ['14', '17'])).
% 2.52/2.71  thf('19', plain, (~ (r1_tarski @ sk_B @ (k5_xboole_0 @ sk_A @ sk_D))),
% 2.52/2.71      inference('demod', [status(thm)], ['0', '18'])).
% 2.52/2.71  thf('20', plain, ((r1_xboole_0 @ sk_D @ sk_C_1)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf(symmetry_r1_xboole_0, axiom,
% 2.52/2.71    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.52/2.71  thf('21', plain,
% 2.52/2.71      (![X5 : $i, X6 : $i]:
% 2.52/2.71         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 2.52/2.71      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.52/2.71  thf('22', plain, ((r1_xboole_0 @ sk_C_1 @ sk_D)),
% 2.52/2.71      inference('sup-', [status(thm)], ['20', '21'])).
% 2.52/2.71  thf('23', plain,
% 2.52/2.71      (((k4_xboole_0 @ sk_A @ sk_D) = (k5_xboole_0 @ sk_A @ sk_D))),
% 2.52/2.71      inference('sup+', [status(thm)], ['10', '13'])).
% 2.52/2.71  thf(t51_xboole_1, axiom,
% 2.52/2.71    (![A:$i,B:$i]:
% 2.52/2.71     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 2.52/2.71       ( A ) ))).
% 2.52/2.71  thf('24', plain,
% 2.52/2.71      (![X21 : $i, X22 : $i]:
% 2.52/2.71         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 2.52/2.71           = (X21))),
% 2.52/2.71      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.52/2.71  thf(commutativity_k2_xboole_0, axiom,
% 2.52/2.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.52/2.71  thf('25', plain,
% 2.52/2.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.52/2.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.52/2.71  thf('26', plain,
% 2.52/2.71      (![X21 : $i, X22 : $i]:
% 2.52/2.71         ((k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ (k3_xboole_0 @ X21 @ X22))
% 2.52/2.71           = (X21))),
% 2.52/2.71      inference('demod', [status(thm)], ['24', '25'])).
% 2.52/2.71  thf('27', plain,
% 2.52/2.71      (((k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_D) @ 
% 2.52/2.71         (k3_xboole_0 @ sk_A @ sk_D)) = (sk_A))),
% 2.52/2.71      inference('sup+', [status(thm)], ['23', '26'])).
% 2.52/2.71  thf('28', plain,
% 2.52/2.71      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.52/2.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.52/2.71  thf('29', plain, (((k3_xboole_0 @ sk_D @ sk_A) = (sk_D))),
% 2.52/2.71      inference('sup-', [status(thm)], ['8', '9'])).
% 2.52/2.71  thf('30', plain,
% 2.52/2.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.52/2.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.52/2.71  thf('31', plain,
% 2.52/2.71      (((k2_xboole_0 @ sk_D @ (k5_xboole_0 @ sk_A @ sk_D)) = (sk_A))),
% 2.52/2.71      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 2.52/2.71  thf('32', plain,
% 2.52/2.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.52/2.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.52/2.71  thf(t73_xboole_1, axiom,
% 2.52/2.71    (![A:$i,B:$i,C:$i]:
% 2.52/2.71     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 2.52/2.71       ( r1_tarski @ A @ B ) ))).
% 2.52/2.71  thf('33', plain,
% 2.52/2.71      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.52/2.71         ((r1_tarski @ X23 @ X24)
% 2.52/2.71          | ~ (r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25))
% 2.52/2.71          | ~ (r1_xboole_0 @ X23 @ X25))),
% 2.52/2.71      inference('cnf', [status(esa)], [t73_xboole_1])).
% 2.52/2.71  thf('34', plain,
% 2.52/2.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.71         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 2.52/2.71          | ~ (r1_xboole_0 @ X2 @ X1)
% 2.52/2.71          | (r1_tarski @ X2 @ X0))),
% 2.52/2.71      inference('sup-', [status(thm)], ['32', '33'])).
% 2.52/2.71  thf('35', plain,
% 2.52/2.71      (![X0 : $i]:
% 2.52/2.71         (~ (r1_tarski @ X0 @ sk_A)
% 2.52/2.71          | (r1_tarski @ X0 @ (k5_xboole_0 @ sk_A @ sk_D))
% 2.52/2.71          | ~ (r1_xboole_0 @ X0 @ sk_D))),
% 2.52/2.71      inference('sup-', [status(thm)], ['31', '34'])).
% 2.52/2.71  thf('36', plain,
% 2.52/2.71      (((r1_tarski @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_D))
% 2.52/2.71        | ~ (r1_tarski @ sk_C_1 @ sk_A))),
% 2.52/2.71      inference('sup-', [status(thm)], ['22', '35'])).
% 2.52/2.71  thf('37', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('38', plain,
% 2.52/2.71      (![X31 : $i, X32 : $i]:
% 2.52/2.71         (~ (m1_subset_1 @ X31 @ X32)
% 2.52/2.71          | (r2_hidden @ X31 @ X32)
% 2.52/2.71          | (v1_xboole_0 @ X32))),
% 2.52/2.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.52/2.71  thf('39', plain,
% 2.52/2.71      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 2.52/2.71        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['37', '38'])).
% 2.52/2.71  thf('40', plain, (![X36 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 2.52/2.71      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.52/2.71  thf('41', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.52/2.71      inference('clc', [status(thm)], ['39', '40'])).
% 2.52/2.71  thf('42', plain,
% 2.52/2.71      (![X27 : $i, X29 : $i]:
% 2.52/2.71         ((r1_tarski @ X29 @ X27) | ~ (r2_hidden @ X29 @ (k1_zfmisc_1 @ X27)))),
% 2.52/2.71      inference('simplify', [status(thm)], ['6'])).
% 2.52/2.71  thf('43', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 2.52/2.71      inference('sup-', [status(thm)], ['41', '42'])).
% 2.52/2.71  thf('44', plain, ((r1_tarski @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_D))),
% 2.52/2.71      inference('demod', [status(thm)], ['36', '43'])).
% 2.52/2.71  thf('45', plain,
% 2.52/2.71      (![X15 : $i, X16 : $i]:
% 2.52/2.71         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 2.52/2.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.52/2.71  thf('46', plain,
% 2.52/2.71      (((k3_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_D)) = (sk_C_1))),
% 2.52/2.71      inference('sup-', [status(thm)], ['44', '45'])).
% 2.52/2.71  thf('47', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('48', plain,
% 2.52/2.71      (![X15 : $i, X16 : $i]:
% 2.52/2.71         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 2.52/2.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.52/2.71  thf('49', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 2.52/2.71      inference('sup-', [status(thm)], ['47', '48'])).
% 2.52/2.71  thf(t16_xboole_1, axiom,
% 2.52/2.71    (![A:$i,B:$i,C:$i]:
% 2.52/2.71     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 2.52/2.71       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.52/2.71  thf('50', plain,
% 2.52/2.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.52/2.71         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 2.52/2.71           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 2.52/2.71      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.52/2.71  thf('51', plain,
% 2.52/2.71      (![X0 : $i]:
% 2.52/2.71         ((k3_xboole_0 @ sk_B @ X0)
% 2.52/2.71           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 2.52/2.71      inference('sup+', [status(thm)], ['49', '50'])).
% 2.52/2.71  thf('52', plain,
% 2.52/2.71      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_D))
% 2.52/2.71         = (k3_xboole_0 @ sk_B @ sk_C_1))),
% 2.52/2.71      inference('sup+', [status(thm)], ['46', '51'])).
% 2.52/2.71  thf('53', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 2.52/2.71      inference('sup-', [status(thm)], ['47', '48'])).
% 2.52/2.71  thf('54', plain,
% 2.52/2.71      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_D)) = (sk_B))),
% 2.52/2.71      inference('demod', [status(thm)], ['52', '53'])).
% 2.52/2.71  thf(idempotence_k3_xboole_0, axiom,
% 2.52/2.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 2.52/2.71  thf('55', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 2.52/2.71      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 2.52/2.71  thf('56', plain,
% 2.52/2.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.52/2.71         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 2.52/2.71           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 2.52/2.71      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.52/2.71  thf('57', plain,
% 2.52/2.71      (![X10 : $i, X11 : $i]:
% 2.52/2.71         ((k4_xboole_0 @ X10 @ X11)
% 2.52/2.71           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 2.52/2.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.52/2.71  thf('58', plain,
% 2.52/2.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.71         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 2.52/2.71           = (k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 2.52/2.71              (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 2.52/2.71      inference('sup+', [status(thm)], ['56', '57'])).
% 2.52/2.71  thf('59', plain,
% 2.52/2.71      (![X0 : $i, X1 : $i]:
% 2.52/2.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 2.52/2.71           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.52/2.71      inference('sup+', [status(thm)], ['55', '58'])).
% 2.52/2.71  thf(t3_boole, axiom,
% 2.52/2.71    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.52/2.71  thf('60', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 2.52/2.71      inference('cnf', [status(esa)], [t3_boole])).
% 2.52/2.71  thf(t48_xboole_1, axiom,
% 2.52/2.71    (![A:$i,B:$i]:
% 2.52/2.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.52/2.71  thf('61', plain,
% 2.52/2.71      (![X19 : $i, X20 : $i]:
% 2.52/2.71         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 2.52/2.71           = (k3_xboole_0 @ X19 @ X20))),
% 2.52/2.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.52/2.71  thf('62', plain,
% 2.52/2.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.52/2.71      inference('sup+', [status(thm)], ['60', '61'])).
% 2.52/2.71  thf('63', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 2.52/2.71      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 2.52/2.71  thf('64', plain,
% 2.52/2.71      (![X10 : $i, X11 : $i]:
% 2.52/2.71         ((k4_xboole_0 @ X10 @ X11)
% 2.52/2.71           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 2.52/2.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.52/2.71  thf('65', plain,
% 2.52/2.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 2.52/2.71      inference('sup+', [status(thm)], ['63', '64'])).
% 2.52/2.71  thf(t2_boole, axiom,
% 2.52/2.71    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.52/2.71  thf('66', plain,
% 2.52/2.71      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 2.52/2.71      inference('cnf', [status(esa)], [t2_boole])).
% 2.52/2.71  thf('67', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.52/2.71      inference('demod', [status(thm)], ['62', '65', '66'])).
% 2.52/2.71  thf('68', plain,
% 2.52/2.71      (![X0 : $i, X1 : $i]:
% 2.52/2.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 2.52/2.71      inference('demod', [status(thm)], ['59', '67'])).
% 2.52/2.71  thf(l32_xboole_1, axiom,
% 2.52/2.71    (![A:$i,B:$i]:
% 2.52/2.71     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.52/2.71  thf('69', plain,
% 2.52/2.71      (![X7 : $i, X8 : $i]:
% 2.52/2.71         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 2.52/2.71      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.52/2.71  thf('70', plain,
% 2.52/2.71      (![X0 : $i, X1 : $i]:
% 2.52/2.71         (((k1_xboole_0) != (k1_xboole_0))
% 2.52/2.71          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 2.52/2.71      inference('sup-', [status(thm)], ['68', '69'])).
% 2.52/2.71  thf('71', plain,
% 2.52/2.71      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.52/2.71      inference('simplify', [status(thm)], ['70'])).
% 2.52/2.71  thf('72', plain, ((r1_tarski @ sk_B @ (k5_xboole_0 @ sk_A @ sk_D))),
% 2.52/2.71      inference('sup+', [status(thm)], ['54', '71'])).
% 2.52/2.71  thf('73', plain, ($false), inference('demod', [status(thm)], ['19', '72'])).
% 2.52/2.71  
% 2.52/2.71  % SZS output end Refutation
% 2.52/2.71  
% 2.52/2.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
