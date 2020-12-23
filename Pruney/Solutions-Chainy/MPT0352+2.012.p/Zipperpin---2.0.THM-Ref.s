%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2ihQFMXnIx

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:09 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 166 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  772 (1420 expanded)
%              Number of equality atoms :   45 (  61 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X33 @ X34 )
        = ( k4_xboole_0 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k4_xboole_0 @ X15 @ X14 ) @ ( k4_xboole_0 @ X15 @ X13 ) ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X33 @ X34 )
        = ( k4_xboole_0 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
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
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ X31 )
      | ( r2_hidden @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X35: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('26',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('27',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( r1_tarski @ X28 @ X26 )
      | ( X27
       != ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('28',plain,(
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ X28 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['26','28'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('35',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['21','45'])).

thf('47',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('48',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['52'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('54',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ X31 )
      | ( r2_hidden @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X35: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('60',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ X28 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('62',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('64',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','66'])).

thf('68',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('75',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['51','75'])).

thf('77',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('78',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k4_xboole_0 @ X15 @ X14 ) @ ( k4_xboole_0 @ X15 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('79',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['46','80'])).

thf('82',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2ihQFMXnIx
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.94  % Solved by: fo/fo7.sh
% 0.75/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.94  % done 1387 iterations in 0.483s
% 0.75/0.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.94  % SZS output start Refutation
% 0.75/0.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.94  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.94  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.75/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.94  thf(t31_subset_1, conjecture,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.94       ( ![C:$i]:
% 0.75/0.94         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.94           ( ( r1_tarski @ B @ C ) <=>
% 0.75/0.94             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.75/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.94    (~( ![A:$i,B:$i]:
% 0.75/0.94        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.94          ( ![C:$i]:
% 0.75/0.94            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.94              ( ( r1_tarski @ B @ C ) <=>
% 0.75/0.94                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.75/0.94    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.75/0.94  thf('0', plain,
% 0.75/0.94      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.94           (k3_subset_1 @ sk_A @ sk_B))
% 0.75/0.94        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('1', plain,
% 0.75/0.94      (~
% 0.75/0.94       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.94         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.75/0.94       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.75/0.94      inference('split', [status(esa)], ['0'])).
% 0.75/0.94  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(d5_subset_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.94       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.75/0.94  thf('3', plain,
% 0.75/0.94      (![X33 : $i, X34 : $i]:
% 0.75/0.94         (((k3_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))
% 0.75/0.94          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 0.75/0.94      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.75/0.94  thf('4', plain,
% 0.75/0.94      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['2', '3'])).
% 0.75/0.94  thf('5', plain,
% 0.75/0.94      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.94         (k3_subset_1 @ sk_A @ sk_B))
% 0.75/0.94        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('6', plain,
% 0.75/0.94      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.75/0.94      inference('split', [status(esa)], ['5'])).
% 0.75/0.94  thf(t34_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( r1_tarski @ A @ B ) =>
% 0.75/0.94       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.75/0.94  thf('7', plain,
% 0.75/0.94      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.75/0.94         (~ (r1_tarski @ X13 @ X14)
% 0.75/0.94          | (r1_tarski @ (k4_xboole_0 @ X15 @ X14) @ (k4_xboole_0 @ X15 @ X13)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.75/0.94  thf('8', plain,
% 0.75/0.94      ((![X0 : $i]:
% 0.75/0.94          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B)))
% 0.75/0.94         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['6', '7'])).
% 0.75/0.94  thf('9', plain,
% 0.75/0.94      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.94         (k4_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['4', '8'])).
% 0.75/0.94  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('11', plain,
% 0.75/0.94      (![X33 : $i, X34 : $i]:
% 0.75/0.94         (((k3_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))
% 0.75/0.94          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 0.75/0.94      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.75/0.94  thf('12', plain,
% 0.75/0.94      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.94      inference('sup-', [status(thm)], ['10', '11'])).
% 0.75/0.94  thf('13', plain,
% 0.75/0.94      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.94         (k3_subset_1 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.75/0.94      inference('demod', [status(thm)], ['9', '12'])).
% 0.75/0.94  thf('14', plain,
% 0.75/0.94      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.94           (k3_subset_1 @ sk_A @ sk_B)))
% 0.75/0.94         <= (~
% 0.75/0.94             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.94               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.75/0.94      inference('split', [status(esa)], ['0'])).
% 0.75/0.94  thf('15', plain,
% 0.75/0.94      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.94         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.75/0.94       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['13', '14'])).
% 0.75/0.94  thf('16', plain,
% 0.75/0.94      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.94         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.75/0.94       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.75/0.94      inference('split', [status(esa)], ['5'])).
% 0.75/0.94  thf('17', plain,
% 0.75/0.94      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['2', '3'])).
% 0.75/0.94  thf(t48_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.75/0.94  thf('18', plain,
% 0.75/0.94      (![X23 : $i, X24 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.75/0.94           = (k3_xboole_0 @ X23 @ X24))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.94  thf('19', plain,
% 0.75/0.94      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.75/0.94         = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.75/0.94      inference('sup+', [status(thm)], ['17', '18'])).
% 0.75/0.94  thf(commutativity_k3_xboole_0, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.75/0.94  thf('20', plain,
% 0.75/0.94      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.94  thf('21', plain,
% 0.75/0.94      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.75/0.94         = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['19', '20'])).
% 0.75/0.94  thf('22', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(d2_subset_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( ( v1_xboole_0 @ A ) =>
% 0.75/0.94         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.75/0.94       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.75/0.94         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.75/0.94  thf('23', plain,
% 0.75/0.94      (![X30 : $i, X31 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X30 @ X31)
% 0.75/0.94          | (r2_hidden @ X30 @ X31)
% 0.75/0.94          | (v1_xboole_0 @ X31))),
% 0.75/0.94      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.75/0.94  thf('24', plain,
% 0.75/0.94      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.94        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['22', '23'])).
% 0.75/0.94  thf(fc1_subset_1, axiom,
% 0.75/0.94    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.75/0.94  thf('25', plain, (![X35 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 0.75/0.94      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.75/0.94  thf('26', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.94      inference('clc', [status(thm)], ['24', '25'])).
% 0.75/0.94  thf(d1_zfmisc_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.75/0.94       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.75/0.94  thf('27', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X28 @ X27)
% 0.75/0.94          | (r1_tarski @ X28 @ X26)
% 0.75/0.94          | ((X27) != (k1_zfmisc_1 @ X26)))),
% 0.75/0.94      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.75/0.94  thf('28', plain,
% 0.75/0.94      (![X26 : $i, X28 : $i]:
% 0.75/0.94         ((r1_tarski @ X28 @ X26) | ~ (r2_hidden @ X28 @ (k1_zfmisc_1 @ X26)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['27'])).
% 0.75/0.94  thf('29', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.75/0.94      inference('sup-', [status(thm)], ['26', '28'])).
% 0.75/0.94  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.75/0.94  thf('30', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.75/0.94      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.75/0.94  thf(t12_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.75/0.94  thf('31', plain,
% 0.75/0.94      (![X10 : $i, X11 : $i]:
% 0.75/0.94         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.75/0.94      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.75/0.94  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['30', '31'])).
% 0.75/0.94  thf(commutativity_k2_xboole_0, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.75/0.94  thf('33', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.94  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['32', '33'])).
% 0.75/0.94  thf(t43_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.75/0.94       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.75/0.94  thf('35', plain,
% 0.75/0.94      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.75/0.94         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.75/0.94          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.75/0.94  thf('36', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (r1_tarski @ X1 @ X0)
% 0.75/0.94          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['34', '35'])).
% 0.75/0.94  thf('37', plain, ((r1_tarski @ (k4_xboole_0 @ sk_C_1 @ sk_A) @ k1_xboole_0)),
% 0.75/0.94      inference('sup-', [status(thm)], ['29', '36'])).
% 0.75/0.94  thf('38', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.75/0.94      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.75/0.94  thf(d10_xboole_0, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/0.94  thf('39', plain,
% 0.75/0.94      (![X4 : $i, X6 : $i]:
% 0.75/0.94         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.75/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.94  thf('40', plain,
% 0.75/0.94      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['38', '39'])).
% 0.75/0.94  thf('41', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['37', '40'])).
% 0.75/0.94  thf('42', plain,
% 0.75/0.94      (![X23 : $i, X24 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.75/0.94           = (k3_xboole_0 @ X23 @ X24))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.94  thf('43', plain,
% 0.75/0.94      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.75/0.94      inference('sup+', [status(thm)], ['41', '42'])).
% 0.75/0.94  thf(t3_boole, axiom,
% 0.75/0.94    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/0.94  thf('44', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.75/0.94  thf('45', plain, (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['43', '44'])).
% 0.75/0.94  thf('46', plain,
% 0.75/0.94      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 0.75/0.94      inference('demod', [status(thm)], ['21', '45'])).
% 0.75/0.94  thf('47', plain,
% 0.75/0.94      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.94      inference('sup-', [status(thm)], ['10', '11'])).
% 0.75/0.94  thf('48', plain,
% 0.75/0.94      (![X23 : $i, X24 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.75/0.94           = (k3_xboole_0 @ X23 @ X24))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.94  thf('49', plain,
% 0.75/0.94      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.75/0.94         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.94      inference('sup+', [status(thm)], ['47', '48'])).
% 0.75/0.94  thf('50', plain,
% 0.75/0.94      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.94  thf('51', plain,
% 0.75/0.94      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.75/0.94         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['49', '50'])).
% 0.75/0.94  thf('52', plain,
% 0.75/0.94      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.75/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.94  thf('53', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.75/0.94      inference('simplify', [status(thm)], ['52'])).
% 0.75/0.94  thf(t11_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.75/0.94  thf('54', plain,
% 0.75/0.94      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.75/0.94         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.75/0.94      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.75/0.94  thf('55', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['53', '54'])).
% 0.75/0.94  thf('56', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('57', plain,
% 0.75/0.94      (![X30 : $i, X31 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X30 @ X31)
% 0.75/0.94          | (r2_hidden @ X30 @ X31)
% 0.75/0.94          | (v1_xboole_0 @ X31))),
% 0.75/0.94      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.75/0.94  thf('58', plain,
% 0.75/0.94      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.94        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['56', '57'])).
% 0.75/0.94  thf('59', plain, (![X35 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 0.75/0.94      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.75/0.94  thf('60', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.94      inference('clc', [status(thm)], ['58', '59'])).
% 0.75/0.94  thf('61', plain,
% 0.75/0.94      (![X26 : $i, X28 : $i]:
% 0.75/0.94         ((r1_tarski @ X28 @ X26) | ~ (r2_hidden @ X28 @ (k1_zfmisc_1 @ X26)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['27'])).
% 0.75/0.94  thf('62', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.75/0.94      inference('sup-', [status(thm)], ['60', '61'])).
% 0.75/0.94  thf('63', plain,
% 0.75/0.94      (![X10 : $i, X11 : $i]:
% 0.75/0.94         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.75/0.94      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.75/0.94  thf('64', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['62', '63'])).
% 0.75/0.94  thf('65', plain,
% 0.75/0.94      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.75/0.94         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.75/0.94      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.75/0.94  thf('66', plain,
% 0.75/0.94      (![X0 : $i]: (~ (r1_tarski @ sk_A @ X0) | (r1_tarski @ sk_B @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['64', '65'])).
% 0.75/0.94  thf('67', plain,
% 0.75/0.94      (![X0 : $i]: (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_A @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['55', '66'])).
% 0.75/0.94  thf('68', plain,
% 0.75/0.94      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.75/0.94         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.75/0.94          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.75/0.94  thf('69', plain,
% 0.75/0.94      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_A) @ X0)),
% 0.75/0.94      inference('sup-', [status(thm)], ['67', '68'])).
% 0.75/0.94  thf('70', plain,
% 0.75/0.94      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['38', '39'])).
% 0.75/0.94  thf('71', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['69', '70'])).
% 0.75/0.94  thf('72', plain,
% 0.75/0.94      (![X23 : $i, X24 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.75/0.94           = (k3_xboole_0 @ X23 @ X24))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.94  thf('73', plain,
% 0.75/0.94      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.75/0.94      inference('sup+', [status(thm)], ['71', '72'])).
% 0.75/0.94  thf('74', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.75/0.94  thf('75', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['73', '74'])).
% 0.75/0.94  thf('76', plain,
% 0.75/0.94      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['51', '75'])).
% 0.75/0.94  thf('77', plain,
% 0.75/0.94      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.94         (k3_subset_1 @ sk_A @ sk_B)))
% 0.75/0.94         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.94               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.75/0.94      inference('split', [status(esa)], ['5'])).
% 0.75/0.94  thf('78', plain,
% 0.75/0.94      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.75/0.94         (~ (r1_tarski @ X13 @ X14)
% 0.75/0.94          | (r1_tarski @ (k4_xboole_0 @ X15 @ X14) @ (k4_xboole_0 @ X15 @ X13)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.75/0.94  thf('79', plain,
% 0.75/0.94      ((![X0 : $i]:
% 0.75/0.94          (r1_tarski @ (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 0.75/0.94           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))))
% 0.75/0.94         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.94               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['77', '78'])).
% 0.75/0.94  thf('80', plain,
% 0.75/0.94      (((r1_tarski @ sk_B @ 
% 0.75/0.94         (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1))))
% 0.75/0.94         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.94               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.75/0.94      inference('sup+', [status(thm)], ['76', '79'])).
% 0.75/0.94  thf('81', plain,
% 0.75/0.94      (((r1_tarski @ sk_B @ sk_C_1))
% 0.75/0.94         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.94               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.75/0.94      inference('sup+', [status(thm)], ['46', '80'])).
% 0.75/0.94  thf('82', plain,
% 0.75/0.94      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.75/0.94      inference('split', [status(esa)], ['0'])).
% 0.75/0.94  thf('83', plain,
% 0.75/0.94      (~
% 0.75/0.94       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.94         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.75/0.94       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['81', '82'])).
% 0.75/0.94  thf('84', plain, ($false),
% 0.75/0.94      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '83'])).
% 0.75/0.94  
% 0.75/0.94  % SZS output end Refutation
% 0.75/0.94  
% 0.75/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
