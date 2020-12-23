%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ML7gApNVpy

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:08 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 188 expanded)
%              Number of leaves         :   30 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  808 (1569 expanded)
%              Number of equality atoms :   40 (  59 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
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
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ X34 )
      | ( r2_hidden @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('35',plain,(
    ! [X38: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('36',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['34','35'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('37',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ( r1_tarski @ X31 @ X29 )
      | ( X30
       != ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('38',plain,(
    ! [X29: $i,X31: $i] :
      ( ( r1_tarski @ X31 @ X29 )
      | ~ ( r2_hidden @ X31 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['36','38'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','43'])).

thf('45',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('47',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X28 @ X29 )
      | ( r2_hidden @ X28 @ X30 )
      | ( X30
       != ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('55',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ( m1_subset_1 @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X38: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('66',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('76',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','78'])).

thf('80',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','79'])).

thf('81',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['30','80'])).

thf('82',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','81'])).

thf('83',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ML7gApNVpy
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.87/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.87/1.03  % Solved by: fo/fo7.sh
% 0.87/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.87/1.03  % done 1654 iterations in 0.582s
% 0.87/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.87/1.03  % SZS output start Refutation
% 0.87/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.87/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.87/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.87/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.87/1.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.87/1.03  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.87/1.03  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.87/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.87/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.87/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.87/1.03  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.87/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.87/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.87/1.03  thf(t31_subset_1, conjecture,
% 0.87/1.03    (![A:$i,B:$i]:
% 0.87/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.87/1.03       ( ![C:$i]:
% 0.87/1.03         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.87/1.03           ( ( r1_tarski @ B @ C ) <=>
% 0.87/1.03             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.87/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.87/1.03    (~( ![A:$i,B:$i]:
% 0.87/1.03        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.87/1.03          ( ![C:$i]:
% 0.87/1.03            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.87/1.03              ( ( r1_tarski @ B @ C ) <=>
% 0.87/1.03                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.87/1.03    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.87/1.03  thf('0', plain,
% 0.87/1.03      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.87/1.03           (k3_subset_1 @ sk_A @ sk_B))
% 0.87/1.03        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 0.87/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.03  thf('1', plain,
% 0.87/1.03      (~
% 0.87/1.03       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.87/1.03         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.87/1.03       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.87/1.03      inference('split', [status(esa)], ['0'])).
% 0.87/1.03  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.87/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.03  thf(d5_subset_1, axiom,
% 0.87/1.03    (![A:$i,B:$i]:
% 0.87/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.87/1.03       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.87/1.03  thf('3', plain,
% 0.87/1.03      (![X36 : $i, X37 : $i]:
% 0.87/1.03         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.87/1.03          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.87/1.03      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.87/1.03  thf('4', plain,
% 0.87/1.03      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.87/1.03      inference('sup-', [status(thm)], ['2', '3'])).
% 0.87/1.03  thf('5', plain,
% 0.87/1.03      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.87/1.03         (k3_subset_1 @ sk_A @ sk_B))
% 0.87/1.03        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.87/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.03  thf('6', plain,
% 0.87/1.03      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.87/1.03      inference('split', [status(esa)], ['5'])).
% 0.87/1.03  thf(t34_xboole_1, axiom,
% 0.87/1.03    (![A:$i,B:$i,C:$i]:
% 0.87/1.03     ( ( r1_tarski @ A @ B ) =>
% 0.87/1.03       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.87/1.03  thf('7', plain,
% 0.87/1.03      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.87/1.03         (~ (r1_tarski @ X13 @ X14)
% 0.87/1.03          | (r1_tarski @ (k4_xboole_0 @ X15 @ X14) @ (k4_xboole_0 @ X15 @ X13)))),
% 0.87/1.03      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.87/1.03  thf('8', plain,
% 0.87/1.03      ((![X0 : $i]:
% 0.87/1.03          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B)))
% 0.87/1.03         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.87/1.03      inference('sup-', [status(thm)], ['6', '7'])).
% 0.87/1.03  thf('9', plain,
% 0.87/1.03      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.87/1.03         (k4_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['4', '8'])).
% 0.87/1.03  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.87/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.03  thf('11', plain,
% 0.87/1.03      (![X36 : $i, X37 : $i]:
% 0.87/1.03         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.87/1.03          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.87/1.03      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.87/1.03  thf('12', plain,
% 0.87/1.03      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.87/1.03      inference('sup-', [status(thm)], ['10', '11'])).
% 0.87/1.03  thf('13', plain,
% 0.87/1.03      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.87/1.03         (k3_subset_1 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.87/1.03      inference('demod', [status(thm)], ['9', '12'])).
% 0.87/1.03  thf('14', plain,
% 0.87/1.03      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.87/1.03           (k3_subset_1 @ sk_A @ sk_B)))
% 0.87/1.03         <= (~
% 0.87/1.03             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.87/1.03               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.87/1.03      inference('split', [status(esa)], ['0'])).
% 0.87/1.03  thf('15', plain,
% 0.87/1.03      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.87/1.03         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.87/1.03       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.87/1.03      inference('sup-', [status(thm)], ['13', '14'])).
% 0.87/1.03  thf('16', plain,
% 0.87/1.03      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.87/1.03         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.87/1.03       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.87/1.03      inference('split', [status(esa)], ['5'])).
% 0.87/1.03  thf('17', plain,
% 0.87/1.03      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.87/1.03         (k3_subset_1 @ sk_A @ sk_B)))
% 0.87/1.03         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.87/1.03               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.87/1.03      inference('split', [status(esa)], ['5'])).
% 0.87/1.03  thf('18', plain,
% 0.87/1.03      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.87/1.03      inference('sup-', [status(thm)], ['2', '3'])).
% 0.87/1.03  thf(t44_xboole_1, axiom,
% 0.87/1.03    (![A:$i,B:$i,C:$i]:
% 0.87/1.03     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.87/1.03       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.87/1.03  thf('19', plain,
% 0.87/1.03      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.87/1.03         ((r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 0.87/1.03          | ~ (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X23))),
% 0.87/1.03      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.87/1.03  thf('20', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ X0)
% 0.87/1.03          | (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 0.87/1.03      inference('sup-', [status(thm)], ['18', '19'])).
% 0.87/1.03  thf('21', plain,
% 0.87/1.03      (((r1_tarski @ sk_A @ 
% 0.87/1.03         (k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.87/1.03         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.87/1.03               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.87/1.03      inference('sup-', [status(thm)], ['17', '20'])).
% 0.87/1.03  thf(commutativity_k2_xboole_0, axiom,
% 0.87/1.03    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.87/1.03  thf('22', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.87/1.03      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.87/1.03  thf(t43_xboole_1, axiom,
% 0.87/1.03    (![A:$i,B:$i,C:$i]:
% 0.87/1.03     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.87/1.03       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.87/1.03  thf('23', plain,
% 0.87/1.03      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.87/1.03         ((r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 0.87/1.03          | ~ (r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 0.87/1.03      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.87/1.03  thf('24', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.03         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.87/1.03          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 0.87/1.03      inference('sup-', [status(thm)], ['22', '23'])).
% 0.87/1.03  thf('25', plain,
% 0.87/1.03      (((r1_tarski @ (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 0.87/1.03         sk_C_1))
% 0.87/1.03         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.87/1.03               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.87/1.03      inference('sup-', [status(thm)], ['21', '24'])).
% 0.87/1.03  thf('26', plain,
% 0.87/1.03      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.87/1.03      inference('sup-', [status(thm)], ['10', '11'])).
% 0.87/1.03  thf(t48_xboole_1, axiom,
% 0.87/1.03    (![A:$i,B:$i]:
% 0.87/1.03     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.87/1.03  thf('27', plain,
% 0.87/1.03      (![X24 : $i, X25 : $i]:
% 0.87/1.03         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.87/1.03           = (k3_xboole_0 @ X24 @ X25))),
% 0.87/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.87/1.03  thf('28', plain,
% 0.87/1.03      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.87/1.03         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.87/1.03      inference('sup+', [status(thm)], ['26', '27'])).
% 0.87/1.03  thf(commutativity_k3_xboole_0, axiom,
% 0.87/1.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.87/1.03  thf('29', plain,
% 0.87/1.03      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.87/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.87/1.03  thf('30', plain,
% 0.87/1.03      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.87/1.03         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.87/1.03      inference('demod', [status(thm)], ['28', '29'])).
% 0.87/1.03  thf(t7_xboole_1, axiom,
% 0.87/1.03    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.87/1.03  thf('31', plain,
% 0.87/1.03      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 0.87/1.03      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.87/1.03  thf('32', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.87/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.03  thf(d2_subset_1, axiom,
% 0.87/1.03    (![A:$i,B:$i]:
% 0.87/1.03     ( ( ( v1_xboole_0 @ A ) =>
% 0.87/1.03         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.87/1.03       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.87/1.03         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.87/1.03  thf('33', plain,
% 0.87/1.03      (![X33 : $i, X34 : $i]:
% 0.87/1.03         (~ (m1_subset_1 @ X33 @ X34)
% 0.87/1.03          | (r2_hidden @ X33 @ X34)
% 0.87/1.03          | (v1_xboole_0 @ X34))),
% 0.87/1.03      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.87/1.03  thf('34', plain,
% 0.87/1.03      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.87/1.03        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.87/1.03      inference('sup-', [status(thm)], ['32', '33'])).
% 0.87/1.03  thf(fc1_subset_1, axiom,
% 0.87/1.03    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.87/1.03  thf('35', plain, (![X38 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 0.87/1.03      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.87/1.03  thf('36', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.87/1.03      inference('clc', [status(thm)], ['34', '35'])).
% 0.87/1.03  thf(d1_zfmisc_1, axiom,
% 0.87/1.03    (![A:$i,B:$i]:
% 0.87/1.03     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.87/1.03       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.87/1.03  thf('37', plain,
% 0.87/1.03      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.87/1.03         (~ (r2_hidden @ X31 @ X30)
% 0.87/1.03          | (r1_tarski @ X31 @ X29)
% 0.87/1.03          | ((X30) != (k1_zfmisc_1 @ X29)))),
% 0.87/1.03      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.87/1.03  thf('38', plain,
% 0.87/1.03      (![X29 : $i, X31 : $i]:
% 0.87/1.03         ((r1_tarski @ X31 @ X29) | ~ (r2_hidden @ X31 @ (k1_zfmisc_1 @ X29)))),
% 0.87/1.03      inference('simplify', [status(thm)], ['37'])).
% 0.87/1.03  thf('39', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.87/1.03      inference('sup-', [status(thm)], ['36', '38'])).
% 0.87/1.03  thf(t12_xboole_1, axiom,
% 0.87/1.03    (![A:$i,B:$i]:
% 0.87/1.03     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.87/1.03  thf('40', plain,
% 0.87/1.03      (![X10 : $i, X11 : $i]:
% 0.87/1.03         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.87/1.03      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.87/1.03  thf('41', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.87/1.03      inference('sup-', [status(thm)], ['39', '40'])).
% 0.87/1.03  thf(t11_xboole_1, axiom,
% 0.87/1.03    (![A:$i,B:$i,C:$i]:
% 0.87/1.03     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.87/1.03  thf('42', plain,
% 0.87/1.03      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.87/1.03         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.87/1.03      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.87/1.03  thf('43', plain,
% 0.87/1.03      (![X0 : $i]: (~ (r1_tarski @ sk_A @ X0) | (r1_tarski @ sk_B @ X0))),
% 0.87/1.03      inference('sup-', [status(thm)], ['41', '42'])).
% 0.87/1.03  thf('44', plain,
% 0.87/1.03      (![X0 : $i]: (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_A @ X0))),
% 0.87/1.03      inference('sup-', [status(thm)], ['31', '43'])).
% 0.87/1.03  thf('45', plain,
% 0.87/1.03      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.87/1.03         ((r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 0.87/1.03          | ~ (r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 0.87/1.03      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.87/1.03  thf('46', plain,
% 0.87/1.03      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_A) @ X0)),
% 0.87/1.03      inference('sup-', [status(thm)], ['44', '45'])).
% 0.87/1.03  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.87/1.03  thf('47', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.87/1.03      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.87/1.03  thf(d10_xboole_0, axiom,
% 0.87/1.03    (![A:$i,B:$i]:
% 0.87/1.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.87/1.03  thf('48', plain,
% 0.87/1.03      (![X4 : $i, X6 : $i]:
% 0.87/1.03         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.87/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.87/1.03  thf('49', plain,
% 0.87/1.03      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.87/1.03      inference('sup-', [status(thm)], ['47', '48'])).
% 0.87/1.03  thf('50', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.87/1.03      inference('sup-', [status(thm)], ['46', '49'])).
% 0.87/1.03  thf('51', plain,
% 0.87/1.03      (![X24 : $i, X25 : $i]:
% 0.87/1.03         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.87/1.03           = (k3_xboole_0 @ X24 @ X25))),
% 0.87/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.87/1.03  thf('52', plain,
% 0.87/1.03      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.87/1.03      inference('sup+', [status(thm)], ['50', '51'])).
% 0.87/1.03  thf('53', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.87/1.03      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.87/1.03  thf('54', plain,
% 0.87/1.03      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.87/1.03         (~ (r1_tarski @ X28 @ X29)
% 0.87/1.03          | (r2_hidden @ X28 @ X30)
% 0.87/1.03          | ((X30) != (k1_zfmisc_1 @ X29)))),
% 0.87/1.03      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.87/1.03  thf('55', plain,
% 0.87/1.03      (![X28 : $i, X29 : $i]:
% 0.87/1.03         ((r2_hidden @ X28 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X28 @ X29))),
% 0.87/1.03      inference('simplify', [status(thm)], ['54'])).
% 0.87/1.03  thf('56', plain,
% 0.87/1.03      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.87/1.03      inference('sup-', [status(thm)], ['53', '55'])).
% 0.87/1.03  thf('57', plain,
% 0.87/1.03      (![X33 : $i, X34 : $i]:
% 0.87/1.03         (~ (r2_hidden @ X33 @ X34)
% 0.87/1.03          | (m1_subset_1 @ X33 @ X34)
% 0.87/1.03          | (v1_xboole_0 @ X34))),
% 0.87/1.03      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.87/1.03  thf('58', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.87/1.03          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.87/1.03      inference('sup-', [status(thm)], ['56', '57'])).
% 0.87/1.03  thf('59', plain, (![X38 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 0.87/1.03      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.87/1.03  thf('60', plain,
% 0.87/1.03      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.87/1.03      inference('clc', [status(thm)], ['58', '59'])).
% 0.87/1.03  thf('61', plain,
% 0.87/1.03      (![X36 : $i, X37 : $i]:
% 0.87/1.03         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.87/1.03          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.87/1.03      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.87/1.03  thf('62', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.87/1.03      inference('sup-', [status(thm)], ['60', '61'])).
% 0.87/1.03  thf('63', plain,
% 0.87/1.03      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.87/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.87/1.03  thf('64', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.87/1.03      inference('simplify', [status(thm)], ['63'])).
% 0.87/1.03  thf('65', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.87/1.03      inference('sup-', [status(thm)], ['60', '61'])).
% 0.87/1.03  thf('66', plain,
% 0.87/1.03      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.87/1.03         ((r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 0.87/1.03          | ~ (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X23))),
% 0.87/1.03      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.87/1.03  thf('67', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         (~ (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X1)
% 0.87/1.03          | (r1_tarski @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.87/1.03      inference('sup-', [status(thm)], ['65', '66'])).
% 0.87/1.03  thf('68', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.87/1.03      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.87/1.03  thf('69', plain,
% 0.87/1.03      (![X10 : $i, X11 : $i]:
% 0.87/1.03         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.87/1.03      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.87/1.03  thf('70', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.87/1.03      inference('sup-', [status(thm)], ['68', '69'])).
% 0.87/1.03  thf('71', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         (~ (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X1)
% 0.87/1.03          | (r1_tarski @ X0 @ X1))),
% 0.87/1.03      inference('demod', [status(thm)], ['67', '70'])).
% 0.87/1.03  thf('72', plain,
% 0.87/1.03      (![X0 : $i]: (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.87/1.03      inference('sup-', [status(thm)], ['64', '71'])).
% 0.87/1.03  thf('73', plain,
% 0.87/1.03      (![X4 : $i, X6 : $i]:
% 0.87/1.03         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.87/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.87/1.03  thf('74', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         (~ (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X0)
% 0.87/1.03          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 0.87/1.03      inference('sup-', [status(thm)], ['72', '73'])).
% 0.87/1.03  thf('75', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.87/1.03      inference('sup-', [status(thm)], ['60', '61'])).
% 0.87/1.03  thf(t36_xboole_1, axiom,
% 0.87/1.03    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.87/1.03  thf('76', plain,
% 0.87/1.03      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.87/1.03      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.87/1.03  thf('77', plain,
% 0.87/1.03      (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X0)),
% 0.87/1.03      inference('sup+', [status(thm)], ['75', '76'])).
% 0.87/1.03  thf('78', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.87/1.03      inference('demod', [status(thm)], ['74', '77'])).
% 0.87/1.03  thf('79', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.87/1.03      inference('demod', [status(thm)], ['62', '78'])).
% 0.87/1.03  thf('80', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.87/1.03      inference('demod', [status(thm)], ['52', '79'])).
% 0.87/1.03  thf('81', plain,
% 0.87/1.03      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.87/1.03      inference('demod', [status(thm)], ['30', '80'])).
% 0.87/1.03  thf('82', plain,
% 0.87/1.03      (((r1_tarski @ sk_B @ sk_C_1))
% 0.87/1.03         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.87/1.03               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.87/1.03      inference('demod', [status(thm)], ['25', '81'])).
% 0.87/1.03  thf('83', plain,
% 0.87/1.03      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.87/1.03      inference('split', [status(esa)], ['0'])).
% 0.87/1.03  thf('84', plain,
% 0.87/1.03      (~
% 0.87/1.03       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.87/1.03         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.87/1.03       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.87/1.03      inference('sup-', [status(thm)], ['82', '83'])).
% 0.87/1.03  thf('85', plain, ($false),
% 0.87/1.03      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '84'])).
% 0.87/1.03  
% 0.87/1.03  % SZS output end Refutation
% 0.87/1.03  
% 0.87/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
