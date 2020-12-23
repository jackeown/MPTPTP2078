%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xBktyDQH0x

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:52 EST 2020

% Result     : Theorem 9.02s
% Output     : Refutation 9.02s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 345 expanded)
%              Number of leaves         :   28 ( 119 expanded)
%              Depth                    :   20
%              Number of atoms          : 1286 (2542 expanded)
%              Number of equality atoms :   72 ( 143 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t41_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) )
      | ( ( k4_subset_1 @ X33 @ X32 @ X34 )
        = ( k2_xboole_0 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X23 )
      | ( X23
       != ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('23',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( m1_subset_1 @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X31: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ ( k4_xboole_0 @ X10 @ X9 ) @ ( k4_xboole_0 @ X10 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_subset_1 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k3_subset_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_subset_1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = ( k3_subset_1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['17','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('49',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('52',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_subset_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X31: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('58',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( r1_tarski @ X24 @ X22 )
      | ( X23
       != ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('60',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ X24 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('63',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('66',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('69',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('70',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( m1_subset_1 @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X31: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['68','77'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('79',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['61','80'])).

thf('82',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ sk_B ) ) @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ sk_B ) ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ ( k3_subset_1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ k1_xboole_0 ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['53','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('89',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( m1_subset_1 @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X31: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','104'])).

thf('106',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('109',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('110',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['108','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['107','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['86','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('118',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('122',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X31: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('124',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ X24 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('126',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','128'])).

thf('130',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ X0 @ sk_A ) )
      = ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('133',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['131','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['116','137'])).

thf('139',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('140',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( m1_subset_1 @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('142',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X31: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('144',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('146',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('149',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('151',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ ( k4_xboole_0 @ X10 @ X9 ) @ ( k4_xboole_0 @ X10 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['149','152'])).

thf('154',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['146','153'])).

thf('155',plain,(
    $false ),
    inference(demod,[status(thm)],['8','154'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xBktyDQH0x
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 9.02/9.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.02/9.24  % Solved by: fo/fo7.sh
% 9.02/9.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.02/9.24  % done 12846 iterations in 8.751s
% 9.02/9.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.02/9.24  % SZS output start Refutation
% 9.02/9.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.02/9.24  thf(sk_C_1_type, type, sk_C_1: $i).
% 9.02/9.24  thf(sk_B_type, type, sk_B: $i).
% 9.02/9.24  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.02/9.24  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 9.02/9.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.02/9.24  thf(sk_A_type, type, sk_A: $i).
% 9.02/9.24  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.02/9.24  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 9.02/9.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.02/9.24  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.02/9.24  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 9.02/9.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.02/9.24  thf(t41_subset_1, conjecture,
% 9.02/9.24    (![A:$i,B:$i]:
% 9.02/9.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.02/9.24       ( ![C:$i]:
% 9.02/9.24         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.02/9.24           ( r1_tarski @
% 9.02/9.24             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 9.02/9.24             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 9.02/9.24  thf(zf_stmt_0, negated_conjecture,
% 9.02/9.24    (~( ![A:$i,B:$i]:
% 9.02/9.24        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.02/9.24          ( ![C:$i]:
% 9.02/9.24            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.02/9.24              ( r1_tarski @
% 9.02/9.24                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 9.02/9.24                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 9.02/9.24    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 9.02/9.24  thf('0', plain,
% 9.02/9.24      (~ (r1_tarski @ 
% 9.02/9.24          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 9.02/9.24          (k3_subset_1 @ sk_A @ sk_B))),
% 9.02/9.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.24  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 9.02/9.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.24  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.02/9.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.24  thf(redefinition_k4_subset_1, axiom,
% 9.02/9.24    (![A:$i,B:$i,C:$i]:
% 9.02/9.24     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 9.02/9.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 9.02/9.24       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 9.02/9.24  thf('3', plain,
% 9.02/9.24      (![X32 : $i, X33 : $i, X34 : $i]:
% 9.02/9.24         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 9.02/9.24          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33))
% 9.02/9.24          | ((k4_subset_1 @ X33 @ X32 @ X34) = (k2_xboole_0 @ X32 @ X34)))),
% 9.02/9.24      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 9.02/9.24  thf('4', plain,
% 9.02/9.24      (![X0 : $i]:
% 9.02/9.24         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 9.02/9.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 9.02/9.24      inference('sup-', [status(thm)], ['2', '3'])).
% 9.02/9.24  thf('5', plain,
% 9.02/9.24      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 9.02/9.24      inference('sup-', [status(thm)], ['1', '4'])).
% 9.02/9.24  thf(commutativity_k2_xboole_0, axiom,
% 9.02/9.24    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 9.02/9.24  thf('6', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.02/9.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.02/9.24  thf('7', plain,
% 9.02/9.24      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_C_1 @ sk_B))),
% 9.02/9.24      inference('demod', [status(thm)], ['5', '6'])).
% 9.02/9.24  thf('8', plain,
% 9.02/9.24      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 9.02/9.24          (k3_subset_1 @ sk_A @ sk_B))),
% 9.02/9.24      inference('demod', [status(thm)], ['0', '7'])).
% 9.02/9.24  thf(t1_boole, axiom,
% 9.02/9.24    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 9.02/9.24  thf('9', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 9.02/9.24      inference('cnf', [status(esa)], [t1_boole])).
% 9.02/9.24  thf(t7_xboole_1, axiom,
% 9.02/9.24    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 9.02/9.24  thf('10', plain,
% 9.02/9.24      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 9.02/9.24      inference('cnf', [status(esa)], [t7_xboole_1])).
% 9.02/9.24  thf('11', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 9.02/9.24      inference('sup+', [status(thm)], ['9', '10'])).
% 9.02/9.24  thf(t43_xboole_1, axiom,
% 9.02/9.24    (![A:$i,B:$i,C:$i]:
% 9.02/9.24     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 9.02/9.24       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 9.02/9.24  thf('12', plain,
% 9.02/9.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.02/9.24         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 9.02/9.24          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 9.02/9.24      inference('cnf', [status(esa)], [t43_xboole_1])).
% 9.02/9.24  thf('13', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 9.02/9.24      inference('sup-', [status(thm)], ['11', '12'])).
% 9.02/9.24  thf(t12_xboole_1, axiom,
% 9.02/9.24    (![A:$i,B:$i]:
% 9.02/9.24     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 9.02/9.24  thf('14', plain,
% 9.02/9.24      (![X2 : $i, X3 : $i]:
% 9.02/9.24         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 9.02/9.24      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.02/9.24  thf('15', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 9.02/9.24           = (X0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['13', '14'])).
% 9.02/9.24  thf('16', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.02/9.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.02/9.24  thf('17', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 9.02/9.24           = (X0))),
% 9.02/9.24      inference('demod', [status(thm)], ['15', '16'])).
% 9.02/9.24  thf('18', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.02/9.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.02/9.24  thf('19', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 9.02/9.24      inference('sup+', [status(thm)], ['9', '10'])).
% 9.02/9.24  thf(d1_zfmisc_1, axiom,
% 9.02/9.24    (![A:$i,B:$i]:
% 9.02/9.24     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 9.02/9.24       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 9.02/9.24  thf('20', plain,
% 9.02/9.24      (![X21 : $i, X22 : $i, X23 : $i]:
% 9.02/9.24         (~ (r1_tarski @ X21 @ X22)
% 9.02/9.24          | (r2_hidden @ X21 @ X23)
% 9.02/9.24          | ((X23) != (k1_zfmisc_1 @ X22)))),
% 9.02/9.24      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 9.02/9.24  thf('21', plain,
% 9.02/9.24      (![X21 : $i, X22 : $i]:
% 9.02/9.24         ((r2_hidden @ X21 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X21 @ X22))),
% 9.02/9.24      inference('simplify', [status(thm)], ['20'])).
% 9.02/9.24  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['19', '21'])).
% 9.02/9.24  thf(d2_subset_1, axiom,
% 9.02/9.24    (![A:$i,B:$i]:
% 9.02/9.24     ( ( ( v1_xboole_0 @ A ) =>
% 9.02/9.24         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 9.02/9.24       ( ( ~( v1_xboole_0 @ A ) ) =>
% 9.02/9.24         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 9.02/9.24  thf('23', plain,
% 9.02/9.24      (![X26 : $i, X27 : $i]:
% 9.02/9.24         (~ (r2_hidden @ X26 @ X27)
% 9.02/9.24          | (m1_subset_1 @ X26 @ X27)
% 9.02/9.24          | (v1_xboole_0 @ X27))),
% 9.02/9.24      inference('cnf', [status(esa)], [d2_subset_1])).
% 9.02/9.24  thf('24', plain,
% 9.02/9.24      (![X0 : $i]:
% 9.02/9.24         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.02/9.24          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 9.02/9.24      inference('sup-', [status(thm)], ['22', '23'])).
% 9.02/9.24  thf(fc1_subset_1, axiom,
% 9.02/9.24    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 9.02/9.24  thf('25', plain, (![X31 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 9.02/9.24      inference('cnf', [status(esa)], [fc1_subset_1])).
% 9.02/9.24  thf('26', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 9.02/9.24      inference('clc', [status(thm)], ['24', '25'])).
% 9.02/9.24  thf(d5_subset_1, axiom,
% 9.02/9.24    (![A:$i,B:$i]:
% 9.02/9.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.02/9.24       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 9.02/9.24  thf('27', plain,
% 9.02/9.24      (![X29 : $i, X30 : $i]:
% 9.02/9.24         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 9.02/9.24          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 9.02/9.24      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.02/9.24  thf('28', plain,
% 9.02/9.24      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['26', '27'])).
% 9.02/9.24  thf('29', plain,
% 9.02/9.24      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 9.02/9.24      inference('cnf', [status(esa)], [t7_xboole_1])).
% 9.02/9.24  thf(t34_xboole_1, axiom,
% 9.02/9.24    (![A:$i,B:$i,C:$i]:
% 9.02/9.24     ( ( r1_tarski @ A @ B ) =>
% 9.02/9.24       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 9.02/9.24  thf('30', plain,
% 9.02/9.24      (![X8 : $i, X9 : $i, X10 : $i]:
% 9.02/9.24         (~ (r1_tarski @ X8 @ X9)
% 9.02/9.24          | (r1_tarski @ (k4_xboole_0 @ X10 @ X9) @ (k4_xboole_0 @ X10 @ X8)))),
% 9.02/9.24      inference('cnf', [status(esa)], [t34_xboole_1])).
% 9.02/9.24  thf('31', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.02/9.24         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 9.02/9.24          (k4_xboole_0 @ X2 @ X1))),
% 9.02/9.24      inference('sup-', [status(thm)], ['29', '30'])).
% 9.02/9.24  thf('32', plain,
% 9.02/9.24      (![X2 : $i, X3 : $i]:
% 9.02/9.24         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 9.02/9.24      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.02/9.24  thf('33', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)) @ 
% 9.02/9.24           (k4_xboole_0 @ X1 @ X0)) = (k4_xboole_0 @ X1 @ X0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['31', '32'])).
% 9.02/9.24  thf('34', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.02/9.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.02/9.24  thf('35', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 9.02/9.24           (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))
% 9.02/9.24           = (k4_xboole_0 @ X1 @ X0))),
% 9.02/9.24      inference('demod', [status(thm)], ['33', '34'])).
% 9.02/9.24  thf('36', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ (k3_subset_1 @ X0 @ X0) @ 
% 9.02/9.24           (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))
% 9.02/9.24           = (k4_xboole_0 @ X0 @ X0))),
% 9.02/9.24      inference('sup+', [status(thm)], ['28', '35'])).
% 9.02/9.24  thf('37', plain,
% 9.02/9.24      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 9.02/9.24      inference('cnf', [status(esa)], [t7_xboole_1])).
% 9.02/9.24  thf('38', plain,
% 9.02/9.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.02/9.24         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 9.02/9.24          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 9.02/9.24      inference('cnf', [status(esa)], [t43_xboole_1])).
% 9.02/9.24  thf('39', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 9.02/9.24      inference('sup-', [status(thm)], ['37', '38'])).
% 9.02/9.24  thf('40', plain,
% 9.02/9.24      (![X2 : $i, X3 : $i]:
% 9.02/9.24         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 9.02/9.24      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.02/9.24  thf('41', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['39', '40'])).
% 9.02/9.24  thf('42', plain,
% 9.02/9.24      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['26', '27'])).
% 9.02/9.24  thf('43', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ (k3_subset_1 @ X1 @ X1) @ X0) = (X0))),
% 9.02/9.24      inference('demod', [status(thm)], ['41', '42'])).
% 9.02/9.24  thf('44', plain,
% 9.02/9.24      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['26', '27'])).
% 9.02/9.24  thf('45', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 9.02/9.24           = (k3_subset_1 @ X0 @ X0))),
% 9.02/9.24      inference('demod', [status(thm)], ['36', '43', '44'])).
% 9.02/9.24  thf('46', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 9.02/9.24           = (k3_subset_1 @ X0 @ X0))),
% 9.02/9.24      inference('sup+', [status(thm)], ['18', '45'])).
% 9.02/9.24  thf('47', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 9.02/9.24           = (k3_subset_1 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ 
% 9.02/9.24              (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 9.02/9.24      inference('sup+', [status(thm)], ['17', '46'])).
% 9.02/9.24  thf('48', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['39', '40'])).
% 9.02/9.24  thf('49', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 9.02/9.24      inference('cnf', [status(esa)], [t1_boole])).
% 9.02/9.24  thf('50', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 9.02/9.24      inference('sup+', [status(thm)], ['48', '49'])).
% 9.02/9.24  thf('51', plain,
% 9.02/9.24      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['26', '27'])).
% 9.02/9.24  thf('52', plain, (![X0 : $i]: ((k1_xboole_0) = (k3_subset_1 @ X0 @ X0))),
% 9.02/9.24      inference('demod', [status(thm)], ['50', '51'])).
% 9.02/9.24  thf('53', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 9.02/9.24           = (k1_xboole_0))),
% 9.02/9.24      inference('demod', [status(thm)], ['47', '52'])).
% 9.02/9.24  thf('54', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.02/9.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.24  thf('55', plain,
% 9.02/9.24      (![X26 : $i, X27 : $i]:
% 9.02/9.24         (~ (m1_subset_1 @ X26 @ X27)
% 9.02/9.24          | (r2_hidden @ X26 @ X27)
% 9.02/9.24          | (v1_xboole_0 @ X27))),
% 9.02/9.24      inference('cnf', [status(esa)], [d2_subset_1])).
% 9.02/9.24  thf('56', plain,
% 9.02/9.24      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 9.02/9.24        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 9.02/9.24      inference('sup-', [status(thm)], ['54', '55'])).
% 9.02/9.24  thf('57', plain, (![X31 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 9.02/9.24      inference('cnf', [status(esa)], [fc1_subset_1])).
% 9.02/9.24  thf('58', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.02/9.24      inference('clc', [status(thm)], ['56', '57'])).
% 9.02/9.24  thf('59', plain,
% 9.02/9.24      (![X22 : $i, X23 : $i, X24 : $i]:
% 9.02/9.24         (~ (r2_hidden @ X24 @ X23)
% 9.02/9.24          | (r1_tarski @ X24 @ X22)
% 9.02/9.24          | ((X23) != (k1_zfmisc_1 @ X22)))),
% 9.02/9.24      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 9.02/9.24  thf('60', plain,
% 9.02/9.24      (![X22 : $i, X24 : $i]:
% 9.02/9.24         ((r1_tarski @ X24 @ X22) | ~ (r2_hidden @ X24 @ (k1_zfmisc_1 @ X22)))),
% 9.02/9.24      inference('simplify', [status(thm)], ['59'])).
% 9.02/9.24  thf('61', plain, ((r1_tarski @ sk_B @ sk_A)),
% 9.02/9.24      inference('sup-', [status(thm)], ['58', '60'])).
% 9.02/9.24  thf('62', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 9.02/9.24      inference('sup+', [status(thm)], ['9', '10'])).
% 9.02/9.24  thf(t44_xboole_1, axiom,
% 9.02/9.24    (![A:$i,B:$i,C:$i]:
% 9.02/9.24     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 9.02/9.24       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 9.02/9.24  thf('63', plain,
% 9.02/9.24      (![X16 : $i, X17 : $i, X18 : $i]:
% 9.02/9.24         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 9.02/9.24          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 9.02/9.24      inference('cnf', [status(esa)], [t44_xboole_1])).
% 9.02/9.24  thf('64', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 9.02/9.24      inference('sup-', [status(thm)], ['62', '63'])).
% 9.02/9.24  thf('65', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.02/9.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.02/9.24  thf('66', plain,
% 9.02/9.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.02/9.24         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 9.02/9.24          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 9.02/9.24      inference('cnf', [status(esa)], [t43_xboole_1])).
% 9.02/9.24  thf('67', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.02/9.24         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 9.02/9.24          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 9.02/9.24      inference('sup-', [status(thm)], ['65', '66'])).
% 9.02/9.24  thf('68', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         (r1_tarski @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 9.02/9.24      inference('sup-', [status(thm)], ['64', '67'])).
% 9.02/9.24  thf(t36_xboole_1, axiom,
% 9.02/9.24    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 9.02/9.24  thf('69', plain,
% 9.02/9.24      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 9.02/9.24      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.02/9.24  thf('70', plain,
% 9.02/9.24      (![X21 : $i, X22 : $i]:
% 9.02/9.24         ((r2_hidden @ X21 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X21 @ X22))),
% 9.02/9.24      inference('simplify', [status(thm)], ['20'])).
% 9.02/9.24  thf('71', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         (r2_hidden @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['69', '70'])).
% 9.02/9.24  thf('72', plain,
% 9.02/9.24      (![X26 : $i, X27 : $i]:
% 9.02/9.24         (~ (r2_hidden @ X26 @ X27)
% 9.02/9.24          | (m1_subset_1 @ X26 @ X27)
% 9.02/9.24          | (v1_xboole_0 @ X27))),
% 9.02/9.24      inference('cnf', [status(esa)], [d2_subset_1])).
% 9.02/9.24  thf('73', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.02/9.24          | (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 9.02/9.24      inference('sup-', [status(thm)], ['71', '72'])).
% 9.02/9.24  thf('74', plain, (![X31 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 9.02/9.24      inference('cnf', [status(esa)], [fc1_subset_1])).
% 9.02/9.24  thf('75', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 9.02/9.24      inference('clc', [status(thm)], ['73', '74'])).
% 9.02/9.24  thf('76', plain,
% 9.02/9.24      (![X29 : $i, X30 : $i]:
% 9.02/9.24         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 9.02/9.24          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 9.02/9.24      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.02/9.24  thf('77', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 9.02/9.24           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 9.02/9.24      inference('sup-', [status(thm)], ['75', '76'])).
% 9.02/9.24  thf('78', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         (r1_tarski @ (k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 9.02/9.24      inference('demod', [status(thm)], ['68', '77'])).
% 9.02/9.24  thf(t1_xboole_1, axiom,
% 9.02/9.24    (![A:$i,B:$i,C:$i]:
% 9.02/9.24     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 9.02/9.24       ( r1_tarski @ A @ C ) ))).
% 9.02/9.24  thf('79', plain,
% 9.02/9.24      (![X5 : $i, X6 : $i, X7 : $i]:
% 9.02/9.24         (~ (r1_tarski @ X5 @ X6)
% 9.02/9.24          | ~ (r1_tarski @ X6 @ X7)
% 9.02/9.24          | (r1_tarski @ X5 @ X7))),
% 9.02/9.24      inference('cnf', [status(esa)], [t1_xboole_1])).
% 9.02/9.24  thf('80', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.02/9.24         ((r1_tarski @ (k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ X2)
% 9.02/9.24          | ~ (r1_tarski @ X0 @ X2))),
% 9.02/9.24      inference('sup-', [status(thm)], ['78', '79'])).
% 9.02/9.24  thf('81', plain,
% 9.02/9.24      (![X0 : $i]:
% 9.02/9.24         (r1_tarski @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ sk_B)) @ sk_A)),
% 9.02/9.24      inference('sup-', [status(thm)], ['61', '80'])).
% 9.02/9.24  thf('82', plain,
% 9.02/9.24      (![X2 : $i, X3 : $i]:
% 9.02/9.24         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 9.02/9.24      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.02/9.24  thf('83', plain,
% 9.02/9.24      (![X0 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ sk_B)) @ sk_A)
% 9.02/9.24           = (sk_A))),
% 9.02/9.24      inference('sup-', [status(thm)], ['81', '82'])).
% 9.02/9.24  thf('84', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.02/9.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.02/9.24  thf('85', plain,
% 9.02/9.24      (![X0 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ sk_A @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ sk_B)))
% 9.02/9.24           = (sk_A))),
% 9.02/9.24      inference('demod', [status(thm)], ['83', '84'])).
% 9.02/9.24  thf('86', plain,
% 9.02/9.24      (![X0 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ sk_A @ 
% 9.02/9.24           (k3_subset_1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ 
% 9.02/9.24            k1_xboole_0))
% 9.02/9.24           = (sk_A))),
% 9.02/9.24      inference('sup+', [status(thm)], ['53', '85'])).
% 9.02/9.24  thf('87', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 9.02/9.24      inference('sup+', [status(thm)], ['9', '10'])).
% 9.02/9.24  thf('88', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.02/9.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.02/9.24  thf('89', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 9.02/9.24      inference('cnf', [status(esa)], [t1_boole])).
% 9.02/9.24  thf('90', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 9.02/9.24      inference('sup+', [status(thm)], ['88', '89'])).
% 9.02/9.24  thf('91', plain,
% 9.02/9.24      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 9.02/9.24      inference('cnf', [status(esa)], [t7_xboole_1])).
% 9.02/9.24  thf('92', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 9.02/9.24      inference('sup+', [status(thm)], ['90', '91'])).
% 9.02/9.24  thf('93', plain,
% 9.02/9.24      (![X21 : $i, X22 : $i]:
% 9.02/9.24         ((r2_hidden @ X21 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X21 @ X22))),
% 9.02/9.24      inference('simplify', [status(thm)], ['20'])).
% 9.02/9.24  thf('94', plain,
% 9.02/9.24      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['92', '93'])).
% 9.02/9.24  thf('95', plain,
% 9.02/9.24      (![X26 : $i, X27 : $i]:
% 9.02/9.24         (~ (r2_hidden @ X26 @ X27)
% 9.02/9.24          | (m1_subset_1 @ X26 @ X27)
% 9.02/9.24          | (v1_xboole_0 @ X27))),
% 9.02/9.24      inference('cnf', [status(esa)], [d2_subset_1])).
% 9.02/9.24  thf('96', plain,
% 9.02/9.24      (![X0 : $i]:
% 9.02/9.24         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.02/9.24          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 9.02/9.24      inference('sup-', [status(thm)], ['94', '95'])).
% 9.02/9.24  thf('97', plain, (![X31 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 9.02/9.24      inference('cnf', [status(esa)], [fc1_subset_1])).
% 9.02/9.24  thf('98', plain,
% 9.02/9.24      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 9.02/9.24      inference('clc', [status(thm)], ['96', '97'])).
% 9.02/9.24  thf('99', plain,
% 9.02/9.24      (![X29 : $i, X30 : $i]:
% 9.02/9.24         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 9.02/9.24          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 9.02/9.24      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.02/9.24  thf('100', plain,
% 9.02/9.24      (![X0 : $i]:
% 9.02/9.24         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['98', '99'])).
% 9.02/9.24  thf('101', plain,
% 9.02/9.24      (![X16 : $i, X17 : $i, X18 : $i]:
% 9.02/9.24         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 9.02/9.24          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 9.02/9.24      inference('cnf', [status(esa)], [t44_xboole_1])).
% 9.02/9.24  thf('102', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         (~ (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X1)
% 9.02/9.24          | (r1_tarski @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 9.02/9.24      inference('sup-', [status(thm)], ['100', '101'])).
% 9.02/9.24  thf('103', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 9.02/9.24      inference('sup+', [status(thm)], ['88', '89'])).
% 9.02/9.24  thf('104', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         (~ (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X1)
% 9.02/9.24          | (r1_tarski @ X0 @ X1))),
% 9.02/9.24      inference('demod', [status(thm)], ['102', '103'])).
% 9.02/9.24  thf('105', plain,
% 9.02/9.24      (![X0 : $i]: (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['87', '104'])).
% 9.02/9.24  thf('106', plain,
% 9.02/9.24      (![X2 : $i, X3 : $i]:
% 9.02/9.24         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 9.02/9.24      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.02/9.24  thf('107', plain,
% 9.02/9.24      (![X0 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 9.02/9.24           = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['105', '106'])).
% 9.02/9.24  thf('108', plain,
% 9.02/9.24      (![X0 : $i]:
% 9.02/9.24         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['98', '99'])).
% 9.02/9.24  thf('109', plain,
% 9.02/9.24      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 9.02/9.24      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.02/9.24  thf('110', plain,
% 9.02/9.24      (![X2 : $i, X3 : $i]:
% 9.02/9.24         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 9.02/9.24      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.02/9.24  thf('111', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['109', '110'])).
% 9.02/9.24  thf('112', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.02/9.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.02/9.24  thf('113', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 9.02/9.24      inference('demod', [status(thm)], ['111', '112'])).
% 9.02/9.24  thf('114', plain,
% 9.02/9.24      (![X0 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (X0))),
% 9.02/9.24      inference('sup+', [status(thm)], ['108', '113'])).
% 9.02/9.24  thf('115', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 9.02/9.24      inference('sup+', [status(thm)], ['107', '114'])).
% 9.02/9.24  thf('116', plain,
% 9.02/9.24      (![X0 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0))
% 9.02/9.24           = (sk_A))),
% 9.02/9.24      inference('demod', [status(thm)], ['86', '115'])).
% 9.02/9.24  thf('117', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.02/9.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.02/9.24  thf('118', plain,
% 9.02/9.24      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 9.02/9.24      inference('cnf', [status(esa)], [t7_xboole_1])).
% 9.02/9.24  thf('119', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 9.02/9.24      inference('sup+', [status(thm)], ['117', '118'])).
% 9.02/9.24  thf('120', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 9.02/9.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.24  thf('121', plain,
% 9.02/9.24      (![X26 : $i, X27 : $i]:
% 9.02/9.24         (~ (m1_subset_1 @ X26 @ X27)
% 9.02/9.24          | (r2_hidden @ X26 @ X27)
% 9.02/9.24          | (v1_xboole_0 @ X27))),
% 9.02/9.24      inference('cnf', [status(esa)], [d2_subset_1])).
% 9.02/9.24  thf('122', plain,
% 9.02/9.24      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 9.02/9.24        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 9.02/9.24      inference('sup-', [status(thm)], ['120', '121'])).
% 9.02/9.24  thf('123', plain, (![X31 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 9.02/9.24      inference('cnf', [status(esa)], [fc1_subset_1])).
% 9.02/9.24  thf('124', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 9.02/9.24      inference('clc', [status(thm)], ['122', '123'])).
% 9.02/9.24  thf('125', plain,
% 9.02/9.24      (![X22 : $i, X24 : $i]:
% 9.02/9.24         ((r1_tarski @ X24 @ X22) | ~ (r2_hidden @ X24 @ (k1_zfmisc_1 @ X22)))),
% 9.02/9.24      inference('simplify', [status(thm)], ['59'])).
% 9.02/9.24  thf('126', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 9.02/9.24      inference('sup-', [status(thm)], ['124', '125'])).
% 9.02/9.24  thf('127', plain,
% 9.02/9.24      (![X5 : $i, X6 : $i, X7 : $i]:
% 9.02/9.24         (~ (r1_tarski @ X5 @ X6)
% 9.02/9.24          | ~ (r1_tarski @ X6 @ X7)
% 9.02/9.24          | (r1_tarski @ X5 @ X7))),
% 9.02/9.24      inference('cnf', [status(esa)], [t1_xboole_1])).
% 9.02/9.24  thf('128', plain,
% 9.02/9.24      (![X0 : $i]: ((r1_tarski @ sk_C_1 @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['126', '127'])).
% 9.02/9.24  thf('129', plain,
% 9.02/9.24      (![X0 : $i]: (r1_tarski @ sk_C_1 @ (k2_xboole_0 @ X0 @ sk_A))),
% 9.02/9.24      inference('sup-', [status(thm)], ['119', '128'])).
% 9.02/9.24  thf('130', plain,
% 9.02/9.24      (![X2 : $i, X3 : $i]:
% 9.02/9.24         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 9.02/9.24      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.02/9.24  thf('131', plain,
% 9.02/9.24      (![X0 : $i]:
% 9.02/9.24         ((k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ X0 @ sk_A))
% 9.02/9.24           = (k2_xboole_0 @ X0 @ sk_A))),
% 9.02/9.24      inference('sup-', [status(thm)], ['129', '130'])).
% 9.02/9.24  thf('132', plain,
% 9.02/9.24      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 9.02/9.24      inference('cnf', [status(esa)], [t7_xboole_1])).
% 9.02/9.24  thf('133', plain,
% 9.02/9.24      (![X16 : $i, X17 : $i, X18 : $i]:
% 9.02/9.24         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 9.02/9.24          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 9.02/9.24      inference('cnf', [status(esa)], [t44_xboole_1])).
% 9.02/9.24  thf('134', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.02/9.24         (r1_tarski @ X2 @ 
% 9.02/9.24          (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 9.02/9.24      inference('sup-', [status(thm)], ['132', '133'])).
% 9.02/9.24  thf('135', plain,
% 9.02/9.24      (![X0 : $i]:
% 9.02/9.24         (r1_tarski @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_A))),
% 9.02/9.24      inference('sup+', [status(thm)], ['131', '134'])).
% 9.02/9.24  thf('136', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.02/9.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.02/9.24  thf('137', plain,
% 9.02/9.24      (![X0 : $i]:
% 9.02/9.24         (r1_tarski @ X0 @ (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1)))),
% 9.02/9.24      inference('demod', [status(thm)], ['135', '136'])).
% 9.02/9.24  thf('138', plain, ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A)),
% 9.02/9.24      inference('sup+', [status(thm)], ['116', '137'])).
% 9.02/9.24  thf('139', plain,
% 9.02/9.24      (![X21 : $i, X22 : $i]:
% 9.02/9.24         ((r2_hidden @ X21 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X21 @ X22))),
% 9.02/9.24      inference('simplify', [status(thm)], ['20'])).
% 9.02/9.24  thf('140', plain,
% 9.02/9.24      ((r2_hidden @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 9.02/9.24      inference('sup-', [status(thm)], ['138', '139'])).
% 9.02/9.24  thf('141', plain,
% 9.02/9.24      (![X26 : $i, X27 : $i]:
% 9.02/9.24         (~ (r2_hidden @ X26 @ X27)
% 9.02/9.24          | (m1_subset_1 @ X26 @ X27)
% 9.02/9.24          | (v1_xboole_0 @ X27))),
% 9.02/9.24      inference('cnf', [status(esa)], [d2_subset_1])).
% 9.02/9.24  thf('142', plain,
% 9.02/9.24      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 9.02/9.24        | (m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 9.02/9.24      inference('sup-', [status(thm)], ['140', '141'])).
% 9.02/9.24  thf('143', plain, (![X31 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 9.02/9.24      inference('cnf', [status(esa)], [fc1_subset_1])).
% 9.02/9.24  thf('144', plain,
% 9.02/9.24      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 9.02/9.24      inference('clc', [status(thm)], ['142', '143'])).
% 9.02/9.24  thf('145', plain,
% 9.02/9.24      (![X29 : $i, X30 : $i]:
% 9.02/9.24         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 9.02/9.24          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 9.02/9.24      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.02/9.24  thf('146', plain,
% 9.02/9.24      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 9.02/9.24         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 9.02/9.24      inference('sup-', [status(thm)], ['144', '145'])).
% 9.02/9.24  thf('147', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.02/9.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.24  thf('148', plain,
% 9.02/9.24      (![X29 : $i, X30 : $i]:
% 9.02/9.24         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 9.02/9.24          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 9.02/9.24      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.02/9.24  thf('149', plain,
% 9.02/9.24      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 9.02/9.24      inference('sup-', [status(thm)], ['147', '148'])).
% 9.02/9.24  thf('150', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 9.02/9.24      inference('sup+', [status(thm)], ['117', '118'])).
% 9.02/9.24  thf('151', plain,
% 9.02/9.24      (![X8 : $i, X9 : $i, X10 : $i]:
% 9.02/9.24         (~ (r1_tarski @ X8 @ X9)
% 9.02/9.24          | (r1_tarski @ (k4_xboole_0 @ X10 @ X9) @ (k4_xboole_0 @ X10 @ X8)))),
% 9.02/9.24      inference('cnf', [status(esa)], [t34_xboole_1])).
% 9.02/9.24  thf('152', plain,
% 9.02/9.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.02/9.24         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 9.02/9.24          (k4_xboole_0 @ X2 @ X0))),
% 9.02/9.24      inference('sup-', [status(thm)], ['150', '151'])).
% 9.02/9.24  thf('153', plain,
% 9.02/9.24      (![X0 : $i]:
% 9.02/9.24         (r1_tarski @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)) @ 
% 9.02/9.24          (k3_subset_1 @ sk_A @ sk_B))),
% 9.02/9.24      inference('sup+', [status(thm)], ['149', '152'])).
% 9.02/9.24  thf('154', plain,
% 9.02/9.24      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 9.02/9.24        (k3_subset_1 @ sk_A @ sk_B))),
% 9.02/9.24      inference('sup+', [status(thm)], ['146', '153'])).
% 9.02/9.24  thf('155', plain, ($false), inference('demod', [status(thm)], ['8', '154'])).
% 9.02/9.24  
% 9.02/9.24  % SZS output end Refutation
% 9.02/9.24  
% 9.02/9.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
