%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BK5kgDpvxI

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:10 EST 2020

% Result     : Theorem 2.52s
% Output     : Refutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 534 expanded)
%              Number of leaves         :   31 ( 169 expanded)
%              Depth                    :   18
%              Number of atoms          :  929 (4576 expanded)
%              Number of equality atoms :   36 ( 200 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ X46 )
      | ( r2_hidden @ X45 @ X46 )
      | ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X50: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X41 @ X40 )
      | ( r1_tarski @ X41 @ X39 )
      | ( X40
       != ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X39: $i,X41: $i] :
      ( ( r1_tarski @ X41 @ X39 )
      | ~ ( r2_hidden @ X41 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k3_subset_1 @ X48 @ X49 )
        = ( k4_xboole_0 @ X48 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ X46 )
      | ( r2_hidden @ X45 @ X46 )
      | ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X50: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('24',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X39: $i,X41: $i] :
      ( ( r1_tarski @ X41 @ X39 )
      | ~ ( r2_hidden @ X41 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('26',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
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
    ! [X48: $i,X49: $i] :
      ( ( ( k3_subset_1 @ X48 @ X49 )
        = ( k4_xboole_0 @ X48 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
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
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','19','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('40',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X28 @ X29 ) @ X29 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ X35 @ X36 )
      | ~ ( r1_xboole_0 @ X35 @ X37 )
      | ( r1_tarski @ X35 @ ( k4_xboole_0 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('46',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('47',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['37','49'])).

thf('51',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['51'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ X32 @ X33 )
      | ( r1_xboole_0 @ X32 @ ( k4_xboole_0 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('54',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('56',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( r1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('60',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('62',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('63',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C_2 @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('67',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_C_2 @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('70',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_tarski @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) )
      | ~ ( r1_xboole_0 @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('71',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) )
    | ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tarski @ sk_B @ sk_C_2 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','71'])).

thf('73',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,
    ( ( r1_tarski @ sk_B @ sk_C_2 )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['36','74'])).

thf('76',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['35','75'])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('78',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('79',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('81',plain,
    ( ( r1_tarski @ sk_B @ sk_C_2 )
   <= ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference(split,[status(esa)],['51'])).

thf('82',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ X32 @ X33 )
      | ( r1_xboole_0 @ X32 @ ( k4_xboole_0 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('83',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_2 ) )
   <= ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('85',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_2 ) @ sk_B )
   <= ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ X35 @ X36 )
      | ~ ( r1_xboole_0 @ X35 @ X37 )
      | ( r1_tarski @ X35 @ ( k4_xboole_0 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('87',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_2 ) @ ( k4_xboole_0 @ X1 @ sk_B ) )
        | ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_2 ) @ X1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ X0 )
        | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ X0 )
        | ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( r1_tarski @ sk_B @ sk_C_2 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['51'])).

thf('92',plain,(
    r1_tarski @ sk_B @ sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['36','74','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ X0 )
      | ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['90','92'])).

thf('94',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['79','93'])).

thf('95',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('96',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['76','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BK5kgDpvxI
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:11:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.52/2.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.52/2.72  % Solved by: fo/fo7.sh
% 2.52/2.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.52/2.72  % done 4732 iterations in 2.252s
% 2.52/2.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.52/2.72  % SZS output start Refutation
% 2.52/2.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.52/2.72  thf(sk_A_type, type, sk_A: $i).
% 2.52/2.72  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.52/2.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.52/2.72  thf(sk_B_type, type, sk_B: $i).
% 2.52/2.72  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.52/2.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.52/2.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.52/2.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.52/2.72  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.52/2.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.52/2.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.52/2.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.52/2.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.52/2.72  thf(t31_subset_1, conjecture,
% 2.52/2.72    (![A:$i,B:$i]:
% 2.52/2.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.52/2.72       ( ![C:$i]:
% 2.52/2.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.52/2.72           ( ( r1_tarski @ B @ C ) <=>
% 2.52/2.72             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 2.52/2.72  thf(zf_stmt_0, negated_conjecture,
% 2.52/2.72    (~( ![A:$i,B:$i]:
% 2.52/2.72        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.52/2.72          ( ![C:$i]:
% 2.52/2.72            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.52/2.72              ( ( r1_tarski @ B @ C ) <=>
% 2.52/2.72                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 2.52/2.72    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 2.52/2.72  thf('0', plain,
% 2.52/2.72      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72           (k3_subset_1 @ sk_A @ sk_B))
% 2.52/2.72        | ~ (r1_tarski @ sk_B @ sk_C_2))),
% 2.52/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.72  thf('1', plain,
% 2.52/2.72      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72           (k3_subset_1 @ sk_A @ sk_B)))
% 2.52/2.72         <= (~
% 2.52/2.72             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.52/2.72      inference('split', [status(esa)], ['0'])).
% 2.52/2.72  thf('2', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 2.52/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.72  thf(d2_subset_1, axiom,
% 2.52/2.72    (![A:$i,B:$i]:
% 2.52/2.72     ( ( ( v1_xboole_0 @ A ) =>
% 2.52/2.72         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 2.52/2.72       ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.52/2.72         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 2.52/2.72  thf('3', plain,
% 2.52/2.72      (![X45 : $i, X46 : $i]:
% 2.52/2.72         (~ (m1_subset_1 @ X45 @ X46)
% 2.52/2.72          | (r2_hidden @ X45 @ X46)
% 2.52/2.72          | (v1_xboole_0 @ X46))),
% 2.52/2.72      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.52/2.72  thf('4', plain,
% 2.52/2.72      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 2.52/2.72        | (r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['2', '3'])).
% 2.52/2.72  thf(fc1_subset_1, axiom,
% 2.52/2.72    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.52/2.72  thf('5', plain, (![X50 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X50))),
% 2.52/2.72      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.52/2.72  thf('6', plain, ((r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 2.52/2.72      inference('clc', [status(thm)], ['4', '5'])).
% 2.52/2.72  thf(d1_zfmisc_1, axiom,
% 2.52/2.72    (![A:$i,B:$i]:
% 2.52/2.72     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 2.52/2.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 2.52/2.72  thf('7', plain,
% 2.52/2.72      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.52/2.72         (~ (r2_hidden @ X41 @ X40)
% 2.52/2.72          | (r1_tarski @ X41 @ X39)
% 2.52/2.72          | ((X40) != (k1_zfmisc_1 @ X39)))),
% 2.52/2.72      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 2.52/2.72  thf('8', plain,
% 2.52/2.72      (![X39 : $i, X41 : $i]:
% 2.52/2.72         ((r1_tarski @ X41 @ X39) | ~ (r2_hidden @ X41 @ (k1_zfmisc_1 @ X39)))),
% 2.52/2.72      inference('simplify', [status(thm)], ['7'])).
% 2.52/2.72  thf('9', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 2.52/2.72      inference('sup-', [status(thm)], ['6', '8'])).
% 2.52/2.72  thf(t28_xboole_1, axiom,
% 2.52/2.72    (![A:$i,B:$i]:
% 2.52/2.72     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.52/2.72  thf('10', plain,
% 2.52/2.72      (![X18 : $i, X19 : $i]:
% 2.52/2.72         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 2.52/2.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.52/2.72  thf('11', plain, (((k3_xboole_0 @ sk_C_2 @ sk_A) = (sk_C_2))),
% 2.52/2.72      inference('sup-', [status(thm)], ['9', '10'])).
% 2.52/2.72  thf(commutativity_k3_xboole_0, axiom,
% 2.52/2.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.52/2.72  thf('12', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.52/2.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.52/2.72  thf(t100_xboole_1, axiom,
% 2.52/2.72    (![A:$i,B:$i]:
% 2.52/2.72     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.52/2.72  thf('13', plain,
% 2.52/2.72      (![X11 : $i, X12 : $i]:
% 2.52/2.72         ((k4_xboole_0 @ X11 @ X12)
% 2.52/2.72           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.52/2.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.52/2.72  thf('14', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i]:
% 2.52/2.72         ((k4_xboole_0 @ X0 @ X1)
% 2.52/2.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.52/2.72      inference('sup+', [status(thm)], ['12', '13'])).
% 2.52/2.72  thf('15', plain,
% 2.52/2.72      (((k4_xboole_0 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 2.52/2.72      inference('sup+', [status(thm)], ['11', '14'])).
% 2.52/2.72  thf('16', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 2.52/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.72  thf(d5_subset_1, axiom,
% 2.52/2.72    (![A:$i,B:$i]:
% 2.52/2.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.52/2.72       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.52/2.72  thf('17', plain,
% 2.52/2.72      (![X48 : $i, X49 : $i]:
% 2.52/2.72         (((k3_subset_1 @ X48 @ X49) = (k4_xboole_0 @ X48 @ X49))
% 2.52/2.72          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X48)))),
% 2.52/2.72      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.52/2.72  thf('18', plain,
% 2.52/2.72      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 2.52/2.72      inference('sup-', [status(thm)], ['16', '17'])).
% 2.52/2.72  thf('19', plain,
% 2.52/2.72      (((k3_subset_1 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 2.52/2.72      inference('sup+', [status(thm)], ['15', '18'])).
% 2.52/2.72  thf('20', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.52/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.72  thf('21', plain,
% 2.52/2.72      (![X45 : $i, X46 : $i]:
% 2.52/2.72         (~ (m1_subset_1 @ X45 @ X46)
% 2.52/2.72          | (r2_hidden @ X45 @ X46)
% 2.52/2.72          | (v1_xboole_0 @ X46))),
% 2.52/2.72      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.52/2.72  thf('22', plain,
% 2.52/2.72      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 2.52/2.72        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['20', '21'])).
% 2.52/2.72  thf('23', plain, (![X50 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X50))),
% 2.52/2.72      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.52/2.72  thf('24', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.52/2.72      inference('clc', [status(thm)], ['22', '23'])).
% 2.52/2.72  thf('25', plain,
% 2.52/2.72      (![X39 : $i, X41 : $i]:
% 2.52/2.72         ((r1_tarski @ X41 @ X39) | ~ (r2_hidden @ X41 @ (k1_zfmisc_1 @ X39)))),
% 2.52/2.72      inference('simplify', [status(thm)], ['7'])).
% 2.52/2.72  thf('26', plain, ((r1_tarski @ sk_B @ sk_A)),
% 2.52/2.72      inference('sup-', [status(thm)], ['24', '25'])).
% 2.52/2.72  thf('27', plain,
% 2.52/2.72      (![X18 : $i, X19 : $i]:
% 2.52/2.72         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 2.52/2.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.52/2.72  thf('28', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 2.52/2.72      inference('sup-', [status(thm)], ['26', '27'])).
% 2.52/2.72  thf('29', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i]:
% 2.52/2.72         ((k4_xboole_0 @ X0 @ X1)
% 2.52/2.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.52/2.72      inference('sup+', [status(thm)], ['12', '13'])).
% 2.52/2.72  thf('30', plain,
% 2.52/2.72      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.52/2.72      inference('sup+', [status(thm)], ['28', '29'])).
% 2.52/2.72  thf('31', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.52/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.72  thf('32', plain,
% 2.52/2.72      (![X48 : $i, X49 : $i]:
% 2.52/2.72         (((k3_subset_1 @ X48 @ X49) = (k4_xboole_0 @ X48 @ X49))
% 2.52/2.72          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X48)))),
% 2.52/2.72      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.52/2.72  thf('33', plain,
% 2.52/2.72      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 2.52/2.72      inference('sup-', [status(thm)], ['31', '32'])).
% 2.52/2.72  thf('34', plain,
% 2.52/2.72      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.52/2.72      inference('sup+', [status(thm)], ['30', '33'])).
% 2.52/2.72  thf('35', plain,
% 2.52/2.72      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 2.52/2.72           (k5_xboole_0 @ sk_A @ sk_B)))
% 2.52/2.72         <= (~
% 2.52/2.72             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.52/2.72      inference('demod', [status(thm)], ['1', '19', '34'])).
% 2.52/2.72  thf('36', plain,
% 2.52/2.72      (~
% 2.52/2.72       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72         (k3_subset_1 @ sk_A @ sk_B))) | 
% 2.52/2.72       ~ ((r1_tarski @ sk_B @ sk_C_2))),
% 2.52/2.72      inference('split', [status(esa)], ['0'])).
% 2.52/2.72  thf('37', plain,
% 2.52/2.72      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.52/2.72      inference('sup+', [status(thm)], ['28', '29'])).
% 2.52/2.72  thf(d10_xboole_0, axiom,
% 2.52/2.72    (![A:$i,B:$i]:
% 2.52/2.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.52/2.72  thf('38', plain,
% 2.52/2.72      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 2.52/2.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.52/2.72  thf('39', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 2.52/2.72      inference('simplify', [status(thm)], ['38'])).
% 2.52/2.72  thf(t79_xboole_1, axiom,
% 2.52/2.72    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 2.52/2.72  thf('40', plain,
% 2.52/2.72      (![X28 : $i, X29 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X28 @ X29) @ X29)),
% 2.52/2.72      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.52/2.72  thf(symmetry_r1_xboole_0, axiom,
% 2.52/2.72    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.52/2.72  thf('41', plain,
% 2.52/2.72      (![X6 : $i, X7 : $i]:
% 2.52/2.72         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 2.52/2.72      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.52/2.72  thf('42', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.52/2.72      inference('sup-', [status(thm)], ['40', '41'])).
% 2.52/2.72  thf(t86_xboole_1, axiom,
% 2.52/2.72    (![A:$i,B:$i,C:$i]:
% 2.52/2.72     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 2.52/2.72       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 2.52/2.72  thf('43', plain,
% 2.52/2.72      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.52/2.72         (~ (r1_tarski @ X35 @ X36)
% 2.52/2.72          | ~ (r1_xboole_0 @ X35 @ X37)
% 2.52/2.72          | (r1_tarski @ X35 @ (k4_xboole_0 @ X36 @ X37)))),
% 2.52/2.72      inference('cnf', [status(esa)], [t86_xboole_1])).
% 2.52/2.72  thf('44', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.72         ((r1_tarski @ X0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 2.52/2.72          | ~ (r1_tarski @ X0 @ X2))),
% 2.52/2.72      inference('sup-', [status(thm)], ['42', '43'])).
% 2.52/2.72  thf('45', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i]:
% 2.52/2.72         (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['39', '44'])).
% 2.52/2.72  thf(t36_xboole_1, axiom,
% 2.52/2.72    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.52/2.72  thf('46', plain,
% 2.52/2.72      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 2.52/2.72      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.52/2.72  thf('47', plain,
% 2.52/2.72      (![X8 : $i, X10 : $i]:
% 2.52/2.72         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 2.52/2.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.52/2.72  thf('48', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i]:
% 2.52/2.72         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.52/2.72          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['46', '47'])).
% 2.52/2.72  thf('49', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i]:
% 2.52/2.72         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['45', '48'])).
% 2.52/2.72  thf('50', plain,
% 2.52/2.72      (((sk_B) = (k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 2.52/2.72      inference('sup+', [status(thm)], ['37', '49'])).
% 2.52/2.72  thf('51', plain,
% 2.52/2.72      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72         (k3_subset_1 @ sk_A @ sk_B))
% 2.52/2.72        | (r1_tarski @ sk_B @ sk_C_2))),
% 2.52/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.72  thf('52', plain,
% 2.52/2.72      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72         (k3_subset_1 @ sk_A @ sk_B)))
% 2.52/2.72         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.52/2.72      inference('split', [status(esa)], ['51'])).
% 2.52/2.72  thf(t85_xboole_1, axiom,
% 2.52/2.72    (![A:$i,B:$i,C:$i]:
% 2.52/2.72     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 2.52/2.72  thf('53', plain,
% 2.52/2.72      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.52/2.72         (~ (r1_tarski @ X32 @ X33)
% 2.52/2.72          | (r1_xboole_0 @ X32 @ (k4_xboole_0 @ X34 @ X33)))),
% 2.52/2.72      inference('cnf', [status(esa)], [t85_xboole_1])).
% 2.52/2.72  thf('54', plain,
% 2.52/2.72      ((![X0 : $i]:
% 2.52/2.72          (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))
% 2.52/2.72         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.52/2.72      inference('sup-', [status(thm)], ['52', '53'])).
% 2.52/2.72  thf('55', plain,
% 2.52/2.72      (((k3_subset_1 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 2.52/2.72      inference('sup+', [status(thm)], ['15', '18'])).
% 2.52/2.72  thf('56', plain,
% 2.52/2.72      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.52/2.72      inference('sup+', [status(thm)], ['30', '33'])).
% 2.52/2.72  thf('57', plain,
% 2.52/2.72      ((![X0 : $i]:
% 2.52/2.72          (r1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 2.52/2.72           (k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))))
% 2.52/2.72         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.52/2.72      inference('demod', [status(thm)], ['54', '55', '56'])).
% 2.52/2.72  thf('58', plain,
% 2.52/2.72      (((r1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C_2) @ sk_B))
% 2.52/2.72         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.52/2.72      inference('sup+', [status(thm)], ['50', '57'])).
% 2.52/2.72  thf('59', plain,
% 2.52/2.72      (![X6 : $i, X7 : $i]:
% 2.52/2.72         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 2.52/2.72      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.52/2.72  thf('60', plain,
% 2.52/2.72      (((r1_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_2)))
% 2.52/2.72         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.52/2.72      inference('sup-', [status(thm)], ['58', '59'])).
% 2.52/2.72  thf('61', plain,
% 2.52/2.72      (((k4_xboole_0 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 2.52/2.72      inference('sup+', [status(thm)], ['11', '14'])).
% 2.52/2.72  thf('62', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 2.52/2.72      inference('simplify', [status(thm)], ['38'])).
% 2.52/2.72  thf(t44_xboole_1, axiom,
% 2.52/2.72    (![A:$i,B:$i,C:$i]:
% 2.52/2.72     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 2.52/2.72       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.52/2.72  thf('63', plain,
% 2.52/2.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.52/2.72         ((r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24))
% 2.52/2.72          | ~ (r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24))),
% 2.52/2.72      inference('cnf', [status(esa)], [t44_xboole_1])).
% 2.52/2.72  thf('64', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i]:
% 2.52/2.72         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['62', '63'])).
% 2.52/2.72  thf('65', plain,
% 2.52/2.72      ((r1_tarski @ sk_A @ 
% 2.52/2.72        (k2_xboole_0 @ sk_C_2 @ (k5_xboole_0 @ sk_A @ sk_C_2)))),
% 2.52/2.72      inference('sup+', [status(thm)], ['61', '64'])).
% 2.52/2.72  thf('66', plain, ((r1_tarski @ sk_B @ sk_A)),
% 2.52/2.72      inference('sup-', [status(thm)], ['24', '25'])).
% 2.52/2.72  thf(t1_xboole_1, axiom,
% 2.52/2.72    (![A:$i,B:$i,C:$i]:
% 2.52/2.72     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.52/2.72       ( r1_tarski @ A @ C ) ))).
% 2.52/2.72  thf('67', plain,
% 2.52/2.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.52/2.72         (~ (r1_tarski @ X15 @ X16)
% 2.52/2.72          | ~ (r1_tarski @ X16 @ X17)
% 2.52/2.72          | (r1_tarski @ X15 @ X17))),
% 2.52/2.72      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.52/2.72  thf('68', plain,
% 2.52/2.72      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 2.52/2.72      inference('sup-', [status(thm)], ['66', '67'])).
% 2.52/2.72  thf('69', plain,
% 2.52/2.72      ((r1_tarski @ sk_B @ 
% 2.52/2.72        (k2_xboole_0 @ sk_C_2 @ (k5_xboole_0 @ sk_A @ sk_C_2)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['65', '68'])).
% 2.52/2.72  thf(t73_xboole_1, axiom,
% 2.52/2.72    (![A:$i,B:$i,C:$i]:
% 2.52/2.72     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 2.52/2.72       ( r1_tarski @ A @ B ) ))).
% 2.52/2.72  thf('70', plain,
% 2.52/2.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.52/2.72         ((r1_tarski @ X25 @ X26)
% 2.52/2.72          | ~ (r1_tarski @ X25 @ (k2_xboole_0 @ X26 @ X27))
% 2.52/2.72          | ~ (r1_xboole_0 @ X25 @ X27))),
% 2.52/2.72      inference('cnf', [status(esa)], [t73_xboole_1])).
% 2.52/2.72  thf('71', plain,
% 2.52/2.72      ((~ (r1_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_2))
% 2.52/2.72        | (r1_tarski @ sk_B @ sk_C_2))),
% 2.52/2.72      inference('sup-', [status(thm)], ['69', '70'])).
% 2.52/2.72  thf('72', plain,
% 2.52/2.72      (((r1_tarski @ sk_B @ sk_C_2))
% 2.52/2.72         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.52/2.72      inference('sup-', [status(thm)], ['60', '71'])).
% 2.52/2.72  thf('73', plain,
% 2.52/2.72      ((~ (r1_tarski @ sk_B @ sk_C_2)) <= (~ ((r1_tarski @ sk_B @ sk_C_2)))),
% 2.52/2.72      inference('split', [status(esa)], ['0'])).
% 2.52/2.72  thf('74', plain,
% 2.52/2.72      (((r1_tarski @ sk_B @ sk_C_2)) | 
% 2.52/2.72       ~
% 2.52/2.72       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72         (k3_subset_1 @ sk_A @ sk_B)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['72', '73'])).
% 2.52/2.72  thf('75', plain,
% 2.52/2.72      (~
% 2.52/2.72       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72         (k3_subset_1 @ sk_A @ sk_B)))),
% 2.52/2.72      inference('sat_resolution*', [status(thm)], ['36', '74'])).
% 2.52/2.72  thf('76', plain,
% 2.52/2.72      (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 2.52/2.72          (k5_xboole_0 @ sk_A @ sk_B))),
% 2.52/2.72      inference('simpl_trail', [status(thm)], ['35', '75'])).
% 2.52/2.72  thf('77', plain,
% 2.52/2.72      (((k4_xboole_0 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 2.52/2.72      inference('sup+', [status(thm)], ['11', '14'])).
% 2.52/2.72  thf('78', plain,
% 2.52/2.72      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 2.52/2.72      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.52/2.72  thf('79', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ sk_A)),
% 2.52/2.72      inference('sup+', [status(thm)], ['77', '78'])).
% 2.52/2.72  thf('80', plain,
% 2.52/2.72      (((k4_xboole_0 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 2.52/2.72      inference('sup+', [status(thm)], ['11', '14'])).
% 2.52/2.72  thf('81', plain,
% 2.52/2.72      (((r1_tarski @ sk_B @ sk_C_2)) <= (((r1_tarski @ sk_B @ sk_C_2)))),
% 2.52/2.72      inference('split', [status(esa)], ['51'])).
% 2.52/2.72  thf('82', plain,
% 2.52/2.72      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.52/2.72         (~ (r1_tarski @ X32 @ X33)
% 2.52/2.72          | (r1_xboole_0 @ X32 @ (k4_xboole_0 @ X34 @ X33)))),
% 2.52/2.72      inference('cnf', [status(esa)], [t85_xboole_1])).
% 2.52/2.72  thf('83', plain,
% 2.52/2.72      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_2)))
% 2.52/2.72         <= (((r1_tarski @ sk_B @ sk_C_2)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['81', '82'])).
% 2.52/2.72  thf('84', plain,
% 2.52/2.72      (![X6 : $i, X7 : $i]:
% 2.52/2.72         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 2.52/2.72      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.52/2.72  thf('85', plain,
% 2.52/2.72      ((![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_2) @ sk_B))
% 2.52/2.72         <= (((r1_tarski @ sk_B @ sk_C_2)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['83', '84'])).
% 2.52/2.72  thf('86', plain,
% 2.52/2.72      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.52/2.72         (~ (r1_tarski @ X35 @ X36)
% 2.52/2.72          | ~ (r1_xboole_0 @ X35 @ X37)
% 2.52/2.72          | (r1_tarski @ X35 @ (k4_xboole_0 @ X36 @ X37)))),
% 2.52/2.72      inference('cnf', [status(esa)], [t86_xboole_1])).
% 2.52/2.72  thf('87', plain,
% 2.52/2.72      ((![X0 : $i, X1 : $i]:
% 2.52/2.72          ((r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_2) @ (k4_xboole_0 @ X1 @ sk_B))
% 2.52/2.72           | ~ (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_2) @ X1)))
% 2.52/2.72         <= (((r1_tarski @ sk_B @ sk_C_2)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['85', '86'])).
% 2.52/2.72  thf('88', plain,
% 2.52/2.72      ((![X0 : $i]:
% 2.52/2.72          (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ X0)
% 2.52/2.72           | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_2) @ 
% 2.52/2.72              (k4_xboole_0 @ X0 @ sk_B))))
% 2.52/2.72         <= (((r1_tarski @ sk_B @ sk_C_2)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['80', '87'])).
% 2.52/2.72  thf('89', plain,
% 2.52/2.72      (((k4_xboole_0 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 2.52/2.72      inference('sup+', [status(thm)], ['11', '14'])).
% 2.52/2.72  thf('90', plain,
% 2.52/2.72      ((![X0 : $i]:
% 2.52/2.72          (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ X0)
% 2.52/2.72           | (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 2.52/2.72              (k4_xboole_0 @ X0 @ sk_B))))
% 2.52/2.72         <= (((r1_tarski @ sk_B @ sk_C_2)))),
% 2.52/2.72      inference('demod', [status(thm)], ['88', '89'])).
% 2.52/2.72  thf('91', plain,
% 2.52/2.72      (((r1_tarski @ sk_B @ sk_C_2)) | 
% 2.52/2.72       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.52/2.72         (k3_subset_1 @ sk_A @ sk_B)))),
% 2.52/2.72      inference('split', [status(esa)], ['51'])).
% 2.52/2.72  thf('92', plain, (((r1_tarski @ sk_B @ sk_C_2))),
% 2.52/2.72      inference('sat_resolution*', [status(thm)], ['36', '74', '91'])).
% 2.52/2.72  thf('93', plain,
% 2.52/2.72      (![X0 : $i]:
% 2.52/2.72         (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ X0)
% 2.52/2.72          | (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 2.52/2.72             (k4_xboole_0 @ X0 @ sk_B)))),
% 2.52/2.72      inference('simpl_trail', [status(thm)], ['90', '92'])).
% 2.52/2.72  thf('94', plain,
% 2.52/2.72      ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ (k4_xboole_0 @ sk_A @ sk_B))),
% 2.52/2.72      inference('sup-', [status(thm)], ['79', '93'])).
% 2.52/2.72  thf('95', plain,
% 2.52/2.72      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.52/2.72      inference('sup+', [status(thm)], ['28', '29'])).
% 2.52/2.72  thf('96', plain,
% 2.52/2.72      ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ (k5_xboole_0 @ sk_A @ sk_B))),
% 2.52/2.72      inference('demod', [status(thm)], ['94', '95'])).
% 2.52/2.72  thf('97', plain, ($false), inference('demod', [status(thm)], ['76', '96'])).
% 2.52/2.72  
% 2.52/2.72  % SZS output end Refutation
% 2.52/2.72  
% 2.52/2.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
