%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KJjTnVXnWQ

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:09 EST 2020

% Result     : Theorem 5.00s
% Output     : Refutation 5.00s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 410 expanded)
%              Number of leaves         :   31 ( 135 expanded)
%              Depth                    :   19
%              Number of atoms          : 1306 (3441 expanded)
%              Number of equality atoms :   68 ( 162 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k3_subset_1 @ X51 @ X52 )
        = ( k4_xboole_0 @ X51 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['5'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ( r1_tarski @ ( k4_xboole_0 @ X25 @ X24 ) @ ( k4_xboole_0 @ X25 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_2 ) @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k3_subset_1 @ X51 @ X52 )
        = ( k4_xboole_0 @ X51 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['5'])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('19',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference('sup+',[status(thm)],['17','18'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('20',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ X43 @ X44 )
      | ( r2_hidden @ X43 @ X45 )
      | ( X45
       != ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r2_hidden @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X43 @ X44 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X48 @ X49 )
      | ( m1_subset_1 @ X48 @ X49 )
      | ( v1_xboole_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X48: $i,X49: $i] :
      ( ( m1_subset_1 @ X48 @ X49 )
      | ~ ( r2_hidden @ X48 @ X49 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k3_subset_1 @ X51 @ X52 )
        = ( k4_xboole_0 @ X51 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ X49 )
      | ( r2_hidden @ X48 @ X49 )
      | ( v1_xboole_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('32',plain,(
    ! [X53: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('33',plain,(
    r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X46 @ X45 )
      | ( r1_tarski @ X46 @ X44 )
      | ( X45
       != ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('35',plain,(
    ! [X44: $i,X46: $i] :
      ( ( r1_tarski @ X46 @ X44 )
      | ~ ( r2_hidden @ X46 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ X37 @ X38 )
      | ( r1_xboole_0 @ X37 @ ( k4_xboole_0 @ X39 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_xboole_0 @ sk_C_2 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['37','41'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ X40 @ X41 )
      | ~ ( r1_xboole_0 @ X40 @ X42 )
      | ( r1_tarski @ X40 @ ( k4_xboole_0 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) )
      | ~ ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ sk_C_2 @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('47',plain,(
    r1_tarski @ sk_C_2 @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) @ sk_C_2 )
    | ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('52',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
    = ( k2_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X35: $i,X36: $i] :
      ( r1_tarski @ X35 @ ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('54',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['33','35'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('55',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_2 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('58',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X30 @ X31 ) @ X32 )
      | ~ ( r1_tarski @ X30 @ ( k2_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('60',plain,(
    ! [X19: $i] :
      ( r1_tarski @ k1_xboole_0 @ X19 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('61',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k4_xboole_0 @ sk_C_2 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('65',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('68',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('71',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','69','70'])).

thf('72',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
    = sk_A ),
    inference(demod,[status(thm)],['52','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('74',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('79',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X30 @ X31 ) @ X32 )
      | ~ ( r1_tarski @ X30 @ ( k2_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('84',plain,(
    ! [X35: $i,X36: $i] :
      ( r1_tarski @ X35 @ ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r2_hidden @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X43 @ X44 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X48: $i,X49: $i] :
      ( ( m1_subset_1 @ X48 @ X49 )
      | ~ ( r2_hidden @ X48 @ X49 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k3_subset_1 @ X51 @ X52 )
        = ( k4_xboole_0 @ X51 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['82','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['81','92'])).

thf('94',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) @ sk_C_2 ),
    inference('sup+',[status(thm)],['72','93'])).

thf('95',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
    = sk_C_2 ),
    inference(demod,[status(thm)],['49','94'])).

thf('96',plain,
    ( sk_C_2
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['28','95'])).

thf('97',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('98',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ( r1_tarski @ ( k4_xboole_0 @ X25 @ X24 ) @ ( k4_xboole_0 @ X25 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('99',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) @ sk_C_2 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('101',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('102',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('103',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r2_hidden @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X43 @ X44 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('105',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X48: $i,X49: $i] :
      ( ( m1_subset_1 @ X48 @ X49 )
      | ~ ( r2_hidden @ X48 @ X49 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('107',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k3_subset_1 @ X51 @ X52 )
        = ( k4_xboole_0 @ X51 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('109',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('111',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('112',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X35: $i,X36: $i] :
      ( r1_tarski @ X35 @ ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('114',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ X49 )
      | ( r2_hidden @ X48 @ X49 )
      | ( v1_xboole_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('116',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X53: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('118',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X44: $i,X46: $i] :
      ( ( r1_tarski @ X46 @ X44 )
      | ~ ( r2_hidden @ X46 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('120',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','122'])).

thf('124',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X30 @ X31 ) @ X32 )
      | ~ ( r1_tarski @ X30 @ ( k2_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('127',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('129',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('133',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['112','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['81','92'])).

thf('136',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('138',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
    | ( sk_B_1
      = ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['118','119'])).

thf('140',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('142',plain,(
    r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ X40 @ X41 )
      | ~ ( r1_xboole_0 @ X40 @ X42 )
      | ( r1_tarski @ X40 @ ( k4_xboole_0 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['139','144'])).

thf('146',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('147',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( sk_B_1
    = ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['138','147'])).

thf('149',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['109','148'])).

thf('150',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['100','149'])).

thf('151',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('152',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KJjTnVXnWQ
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:38:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.00/5.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.00/5.19  % Solved by: fo/fo7.sh
% 5.00/5.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.00/5.19  % done 14003 iterations in 4.723s
% 5.00/5.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.00/5.19  % SZS output start Refutation
% 5.00/5.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.00/5.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.00/5.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.00/5.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.00/5.19  thf(sk_C_2_type, type, sk_C_2: $i).
% 5.00/5.19  thf(sk_A_type, type, sk_A: $i).
% 5.00/5.19  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.00/5.19  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.00/5.19  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.00/5.19  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.00/5.19  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.00/5.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.00/5.19  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 5.00/5.19  thf(t31_subset_1, conjecture,
% 5.00/5.19    (![A:$i,B:$i]:
% 5.00/5.19     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.00/5.19       ( ![C:$i]:
% 5.00/5.19         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.00/5.19           ( ( r1_tarski @ B @ C ) <=>
% 5.00/5.19             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 5.00/5.19  thf(zf_stmt_0, negated_conjecture,
% 5.00/5.19    (~( ![A:$i,B:$i]:
% 5.00/5.19        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.00/5.19          ( ![C:$i]:
% 5.00/5.19            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.00/5.19              ( ( r1_tarski @ B @ C ) <=>
% 5.00/5.19                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 5.00/5.19    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 5.00/5.19  thf('0', plain,
% 5.00/5.19      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 5.00/5.19           (k3_subset_1 @ sk_A @ sk_B_1))
% 5.00/5.19        | ~ (r1_tarski @ sk_B_1 @ sk_C_2))),
% 5.00/5.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.00/5.19  thf('1', plain,
% 5.00/5.19      (~
% 5.00/5.19       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 5.00/5.19         (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 5.00/5.19       ~ ((r1_tarski @ sk_B_1 @ sk_C_2))),
% 5.00/5.19      inference('split', [status(esa)], ['0'])).
% 5.00/5.19  thf('2', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 5.00/5.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.00/5.19  thf(d5_subset_1, axiom,
% 5.00/5.19    (![A:$i,B:$i]:
% 5.00/5.19     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.00/5.19       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 5.00/5.19  thf('3', plain,
% 5.00/5.19      (![X51 : $i, X52 : $i]:
% 5.00/5.19         (((k3_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))
% 5.00/5.19          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X51)))),
% 5.00/5.19      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.00/5.19  thf('4', plain,
% 5.00/5.19      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 5.00/5.19      inference('sup-', [status(thm)], ['2', '3'])).
% 5.00/5.19  thf('5', plain,
% 5.00/5.19      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 5.00/5.19         (k3_subset_1 @ sk_A @ sk_B_1))
% 5.00/5.19        | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 5.00/5.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.00/5.19  thf('6', plain,
% 5.00/5.19      (((r1_tarski @ sk_B_1 @ sk_C_2)) <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 5.00/5.19      inference('split', [status(esa)], ['5'])).
% 5.00/5.19  thf(t34_xboole_1, axiom,
% 5.00/5.19    (![A:$i,B:$i,C:$i]:
% 5.00/5.19     ( ( r1_tarski @ A @ B ) =>
% 5.00/5.19       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 5.00/5.19  thf('7', plain,
% 5.00/5.19      (![X23 : $i, X24 : $i, X25 : $i]:
% 5.00/5.19         (~ (r1_tarski @ X23 @ X24)
% 5.00/5.19          | (r1_tarski @ (k4_xboole_0 @ X25 @ X24) @ (k4_xboole_0 @ X25 @ X23)))),
% 5.00/5.19      inference('cnf', [status(esa)], [t34_xboole_1])).
% 5.00/5.19  thf('8', plain,
% 5.00/5.19      ((![X0 : $i]:
% 5.00/5.19          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_2) @ 
% 5.00/5.19           (k4_xboole_0 @ X0 @ sk_B_1)))
% 5.00/5.19         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 5.00/5.19      inference('sup-', [status(thm)], ['6', '7'])).
% 5.00/5.19  thf('9', plain,
% 5.00/5.19      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 5.00/5.19         (k4_xboole_0 @ sk_A @ sk_B_1))) <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 5.00/5.19      inference('sup+', [status(thm)], ['4', '8'])).
% 5.00/5.19  thf('10', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 5.00/5.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.00/5.19  thf('11', plain,
% 5.00/5.19      (![X51 : $i, X52 : $i]:
% 5.00/5.19         (((k3_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))
% 5.00/5.19          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X51)))),
% 5.00/5.19      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.00/5.19  thf('12', plain,
% 5.00/5.19      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 5.00/5.19      inference('sup-', [status(thm)], ['10', '11'])).
% 5.00/5.19  thf('13', plain,
% 5.00/5.19      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 5.00/5.19         (k3_subset_1 @ sk_A @ sk_B_1))) <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 5.00/5.19      inference('demod', [status(thm)], ['9', '12'])).
% 5.00/5.19  thf('14', plain,
% 5.00/5.19      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 5.00/5.19           (k3_subset_1 @ sk_A @ sk_B_1)))
% 5.00/5.19         <= (~
% 5.00/5.19             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 5.00/5.19               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 5.00/5.19      inference('split', [status(esa)], ['0'])).
% 5.00/5.19  thf('15', plain,
% 5.00/5.19      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 5.00/5.19         (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 5.00/5.19       ~ ((r1_tarski @ sk_B_1 @ sk_C_2))),
% 5.00/5.19      inference('sup-', [status(thm)], ['13', '14'])).
% 5.00/5.19  thf('16', plain,
% 5.00/5.19      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 5.00/5.19         (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 5.00/5.19       ((r1_tarski @ sk_B_1 @ sk_C_2))),
% 5.00/5.19      inference('split', [status(esa)], ['5'])).
% 5.00/5.19  thf('17', plain,
% 5.00/5.19      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 5.00/5.19      inference('sup-', [status(thm)], ['2', '3'])).
% 5.00/5.19  thf(t36_xboole_1, axiom,
% 5.00/5.19    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 5.00/5.19  thf('18', plain,
% 5.00/5.19      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 5.00/5.19      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.00/5.19  thf('19', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ sk_A)),
% 5.00/5.19      inference('sup+', [status(thm)], ['17', '18'])).
% 5.00/5.19  thf(d1_zfmisc_1, axiom,
% 5.00/5.19    (![A:$i,B:$i]:
% 5.00/5.19     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 5.00/5.19       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 5.00/5.19  thf('20', plain,
% 5.00/5.19      (![X43 : $i, X44 : $i, X45 : $i]:
% 5.00/5.19         (~ (r1_tarski @ X43 @ X44)
% 5.00/5.19          | (r2_hidden @ X43 @ X45)
% 5.00/5.19          | ((X45) != (k1_zfmisc_1 @ X44)))),
% 5.00/5.19      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 5.00/5.19  thf('21', plain,
% 5.00/5.19      (![X43 : $i, X44 : $i]:
% 5.00/5.19         ((r2_hidden @ X43 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X43 @ X44))),
% 5.00/5.19      inference('simplify', [status(thm)], ['20'])).
% 5.00/5.19  thf('22', plain,
% 5.00/5.19      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 5.00/5.19      inference('sup-', [status(thm)], ['19', '21'])).
% 5.00/5.19  thf(d2_subset_1, axiom,
% 5.00/5.19    (![A:$i,B:$i]:
% 5.00/5.19     ( ( ( v1_xboole_0 @ A ) =>
% 5.00/5.19         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 5.00/5.19       ( ( ~( v1_xboole_0 @ A ) ) =>
% 5.00/5.19         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 5.00/5.19  thf('23', plain,
% 5.00/5.19      (![X48 : $i, X49 : $i]:
% 5.00/5.19         (~ (r2_hidden @ X48 @ X49)
% 5.00/5.19          | (m1_subset_1 @ X48 @ X49)
% 5.00/5.19          | (v1_xboole_0 @ X49))),
% 5.00/5.19      inference('cnf', [status(esa)], [d2_subset_1])).
% 5.00/5.19  thf(d1_xboole_0, axiom,
% 5.00/5.19    (![A:$i]:
% 5.00/5.19     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 5.00/5.19  thf('24', plain,
% 5.00/5.19      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 5.00/5.19      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.00/5.19  thf('25', plain,
% 5.00/5.19      (![X48 : $i, X49 : $i]:
% 5.00/5.19         ((m1_subset_1 @ X48 @ X49) | ~ (r2_hidden @ X48 @ X49))),
% 5.00/5.19      inference('clc', [status(thm)], ['23', '24'])).
% 5.00/5.19  thf('26', plain,
% 5.00/5.19      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 5.00/5.19      inference('sup-', [status(thm)], ['22', '25'])).
% 5.00/5.19  thf('27', plain,
% 5.00/5.19      (![X51 : $i, X52 : $i]:
% 5.00/5.19         (((k3_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))
% 5.00/5.19          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X51)))),
% 5.00/5.19      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.00/5.19  thf('28', plain,
% 5.00/5.19      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_2))
% 5.00/5.19         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 5.00/5.19      inference('sup-', [status(thm)], ['26', '27'])).
% 5.00/5.19  thf('29', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 5.00/5.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.00/5.19  thf('30', plain,
% 5.00/5.19      (![X48 : $i, X49 : $i]:
% 5.00/5.19         (~ (m1_subset_1 @ X48 @ X49)
% 5.00/5.19          | (r2_hidden @ X48 @ X49)
% 5.00/5.19          | (v1_xboole_0 @ X49))),
% 5.00/5.19      inference('cnf', [status(esa)], [d2_subset_1])).
% 5.00/5.19  thf('31', plain,
% 5.00/5.19      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 5.00/5.19        | (r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A)))),
% 5.00/5.19      inference('sup-', [status(thm)], ['29', '30'])).
% 5.00/5.19  thf(fc1_subset_1, axiom,
% 5.00/5.19    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 5.00/5.19  thf('32', plain, (![X53 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X53))),
% 5.00/5.19      inference('cnf', [status(esa)], [fc1_subset_1])).
% 5.00/5.19  thf('33', plain, ((r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 5.00/5.19      inference('clc', [status(thm)], ['31', '32'])).
% 5.00/5.19  thf('34', plain,
% 5.00/5.19      (![X44 : $i, X45 : $i, X46 : $i]:
% 5.00/5.19         (~ (r2_hidden @ X46 @ X45)
% 5.00/5.19          | (r1_tarski @ X46 @ X44)
% 5.00/5.19          | ((X45) != (k1_zfmisc_1 @ X44)))),
% 5.00/5.19      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 5.00/5.19  thf('35', plain,
% 5.00/5.19      (![X44 : $i, X46 : $i]:
% 5.00/5.19         ((r1_tarski @ X46 @ X44) | ~ (r2_hidden @ X46 @ (k1_zfmisc_1 @ X44)))),
% 5.00/5.19      inference('simplify', [status(thm)], ['34'])).
% 5.00/5.19  thf('36', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 5.00/5.19      inference('sup-', [status(thm)], ['33', '35'])).
% 5.00/5.19  thf('37', plain,
% 5.00/5.19      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 5.00/5.19      inference('sup-', [status(thm)], ['2', '3'])).
% 5.00/5.19  thf(d10_xboole_0, axiom,
% 5.00/5.19    (![A:$i,B:$i]:
% 5.00/5.19     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.00/5.19  thf('38', plain,
% 5.00/5.19      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 5.00/5.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.00/5.19  thf('39', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 5.00/5.19      inference('simplify', [status(thm)], ['38'])).
% 5.00/5.19  thf(t85_xboole_1, axiom,
% 5.00/5.19    (![A:$i,B:$i,C:$i]:
% 5.00/5.19     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 5.00/5.19  thf('40', plain,
% 5.00/5.19      (![X37 : $i, X38 : $i, X39 : $i]:
% 5.00/5.19         (~ (r1_tarski @ X37 @ X38)
% 5.00/5.19          | (r1_xboole_0 @ X37 @ (k4_xboole_0 @ X39 @ X38)))),
% 5.00/5.19      inference('cnf', [status(esa)], [t85_xboole_1])).
% 5.00/5.19  thf('41', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 5.00/5.19      inference('sup-', [status(thm)], ['39', '40'])).
% 5.00/5.19  thf('42', plain, ((r1_xboole_0 @ sk_C_2 @ (k3_subset_1 @ sk_A @ sk_C_2))),
% 5.00/5.19      inference('sup+', [status(thm)], ['37', '41'])).
% 5.00/5.19  thf(t86_xboole_1, axiom,
% 5.00/5.19    (![A:$i,B:$i,C:$i]:
% 5.00/5.19     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 5.00/5.19       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 5.00/5.19  thf('43', plain,
% 5.00/5.19      (![X40 : $i, X41 : $i, X42 : $i]:
% 5.00/5.19         (~ (r1_tarski @ X40 @ X41)
% 5.00/5.19          | ~ (r1_xboole_0 @ X40 @ X42)
% 5.00/5.19          | (r1_tarski @ X40 @ (k4_xboole_0 @ X41 @ X42)))),
% 5.00/5.19      inference('cnf', [status(esa)], [t86_xboole_1])).
% 5.00/5.19  thf('44', plain,
% 5.00/5.19      (![X0 : $i]:
% 5.00/5.19         ((r1_tarski @ sk_C_2 @ 
% 5.00/5.19           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_2)))
% 5.00/5.19          | ~ (r1_tarski @ sk_C_2 @ X0))),
% 5.00/5.19      inference('sup-', [status(thm)], ['42', '43'])).
% 5.00/5.19  thf('45', plain,
% 5.00/5.19      ((r1_tarski @ sk_C_2 @ 
% 5.00/5.19        (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 5.00/5.19      inference('sup-', [status(thm)], ['36', '44'])).
% 5.00/5.19  thf('46', plain,
% 5.00/5.19      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_2))
% 5.00/5.19         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 5.00/5.19      inference('sup-', [status(thm)], ['26', '27'])).
% 5.00/5.19  thf('47', plain,
% 5.00/5.19      ((r1_tarski @ sk_C_2 @ 
% 5.00/5.19        (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 5.00/5.19      inference('demod', [status(thm)], ['45', '46'])).
% 5.00/5.19  thf('48', plain,
% 5.00/5.19      (![X9 : $i, X11 : $i]:
% 5.00/5.19         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 5.00/5.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.00/5.19  thf('49', plain,
% 5.00/5.19      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_2)) @ 
% 5.00/5.19           sk_C_2)
% 5.00/5.19        | ((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_2)) = (sk_C_2)))),
% 5.00/5.19      inference('sup-', [status(thm)], ['47', '48'])).
% 5.00/5.19  thf('50', plain,
% 5.00/5.19      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 5.00/5.19      inference('sup-', [status(thm)], ['2', '3'])).
% 5.00/5.19  thf(t39_xboole_1, axiom,
% 5.00/5.19    (![A:$i,B:$i]:
% 5.00/5.19     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 5.00/5.19  thf('51', plain,
% 5.00/5.19      (![X28 : $i, X29 : $i]:
% 5.00/5.19         ((k2_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28))
% 5.00/5.19           = (k2_xboole_0 @ X28 @ X29))),
% 5.00/5.19      inference('cnf', [status(esa)], [t39_xboole_1])).
% 5.00/5.19  thf('52', plain,
% 5.00/5.19      (((k2_xboole_0 @ sk_C_2 @ (k3_subset_1 @ sk_A @ sk_C_2))
% 5.00/5.19         = (k2_xboole_0 @ sk_C_2 @ sk_A))),
% 5.00/5.19      inference('sup+', [status(thm)], ['50', '51'])).
% 5.00/5.19  thf(t7_xboole_1, axiom,
% 5.00/5.19    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 5.00/5.19  thf('53', plain,
% 5.00/5.19      (![X35 : $i, X36 : $i]: (r1_tarski @ X35 @ (k2_xboole_0 @ X35 @ X36))),
% 5.00/5.19      inference('cnf', [status(esa)], [t7_xboole_1])).
% 5.00/5.19  thf('54', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 5.00/5.19      inference('sup-', [status(thm)], ['33', '35'])).
% 5.00/5.19  thf(t1_xboole_1, axiom,
% 5.00/5.19    (![A:$i,B:$i,C:$i]:
% 5.00/5.19     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 5.00/5.19       ( r1_tarski @ A @ C ) ))).
% 5.00/5.19  thf('55', plain,
% 5.00/5.19      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.00/5.19         (~ (r1_tarski @ X16 @ X17)
% 5.00/5.19          | ~ (r1_tarski @ X17 @ X18)
% 5.00/5.19          | (r1_tarski @ X16 @ X18))),
% 5.00/5.19      inference('cnf', [status(esa)], [t1_xboole_1])).
% 5.00/5.19  thf('56', plain,
% 5.00/5.19      (![X0 : $i]: ((r1_tarski @ sk_C_2 @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 5.00/5.19      inference('sup-', [status(thm)], ['54', '55'])).
% 5.00/5.19  thf('57', plain,
% 5.00/5.19      (![X0 : $i]: (r1_tarski @ sk_C_2 @ (k2_xboole_0 @ sk_A @ X0))),
% 5.00/5.19      inference('sup-', [status(thm)], ['53', '56'])).
% 5.00/5.19  thf(t43_xboole_1, axiom,
% 5.00/5.19    (![A:$i,B:$i,C:$i]:
% 5.00/5.19     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 5.00/5.19       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 5.00/5.19  thf('58', plain,
% 5.00/5.19      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.00/5.19         ((r1_tarski @ (k4_xboole_0 @ X30 @ X31) @ X32)
% 5.00/5.19          | ~ (r1_tarski @ X30 @ (k2_xboole_0 @ X31 @ X32)))),
% 5.00/5.19      inference('cnf', [status(esa)], [t43_xboole_1])).
% 5.00/5.19  thf('59', plain,
% 5.00/5.19      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C_2 @ sk_A) @ X0)),
% 5.00/5.19      inference('sup-', [status(thm)], ['57', '58'])).
% 5.00/5.19  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.00/5.19  thf('60', plain, (![X19 : $i]: (r1_tarski @ k1_xboole_0 @ X19)),
% 5.00/5.19      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.00/5.19  thf('61', plain,
% 5.00/5.19      (![X9 : $i, X11 : $i]:
% 5.00/5.19         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 5.00/5.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.00/5.19  thf('62', plain,
% 5.00/5.19      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.00/5.19      inference('sup-', [status(thm)], ['60', '61'])).
% 5.00/5.19  thf('63', plain, (((k4_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0))),
% 5.00/5.19      inference('sup-', [status(thm)], ['59', '62'])).
% 5.00/5.19  thf('64', plain,
% 5.00/5.19      (![X28 : $i, X29 : $i]:
% 5.00/5.19         ((k2_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28))
% 5.00/5.19           = (k2_xboole_0 @ X28 @ X29))),
% 5.00/5.19      inference('cnf', [status(esa)], [t39_xboole_1])).
% 5.00/5.19  thf('65', plain,
% 5.00/5.19      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_C_2))),
% 5.00/5.19      inference('sup+', [status(thm)], ['63', '64'])).
% 5.00/5.19  thf(commutativity_k2_xboole_0, axiom,
% 5.00/5.19    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 5.00/5.19  thf('66', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.00/5.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.00/5.19  thf('67', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.00/5.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.00/5.19  thf(t1_boole, axiom,
% 5.00/5.19    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.00/5.19  thf('68', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 5.00/5.19      inference('cnf', [status(esa)], [t1_boole])).
% 5.00/5.19  thf('69', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 5.00/5.19      inference('sup+', [status(thm)], ['67', '68'])).
% 5.00/5.19  thf('70', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.00/5.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.00/5.19  thf('71', plain, (((sk_A) = (k2_xboole_0 @ sk_C_2 @ sk_A))),
% 5.00/5.19      inference('demod', [status(thm)], ['65', '66', '69', '70'])).
% 5.00/5.19  thf('72', plain,
% 5.00/5.19      (((k2_xboole_0 @ sk_C_2 @ (k3_subset_1 @ sk_A @ sk_C_2)) = (sk_A))),
% 5.00/5.19      inference('demod', [status(thm)], ['52', '71'])).
% 5.00/5.19  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 5.00/5.19      inference('sup+', [status(thm)], ['67', '68'])).
% 5.00/5.19  thf('74', plain,
% 5.00/5.19      (![X28 : $i, X29 : $i]:
% 5.00/5.19         ((k2_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28))
% 5.00/5.19           = (k2_xboole_0 @ X28 @ X29))),
% 5.00/5.19      inference('cnf', [status(esa)], [t39_xboole_1])).
% 5.00/5.19  thf('75', plain,
% 5.00/5.19      (![X0 : $i]:
% 5.00/5.19         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 5.00/5.19      inference('sup+', [status(thm)], ['73', '74'])).
% 5.00/5.19  thf('76', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 5.00/5.19      inference('sup+', [status(thm)], ['67', '68'])).
% 5.00/5.19  thf('77', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.00/5.19      inference('demod', [status(thm)], ['75', '76'])).
% 5.00/5.19  thf('78', plain,
% 5.00/5.19      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 5.00/5.19      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.00/5.19  thf('79', plain,
% 5.00/5.19      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.00/5.19         ((r1_tarski @ (k4_xboole_0 @ X30 @ X31) @ X32)
% 5.00/5.19          | ~ (r1_tarski @ X30 @ (k2_xboole_0 @ X31 @ X32)))),
% 5.00/5.19      inference('cnf', [status(esa)], [t43_xboole_1])).
% 5.00/5.19  thf('80', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.00/5.19         (r1_tarski @ 
% 5.00/5.19          (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1) @ 
% 5.00/5.19          X0)),
% 5.00/5.19      inference('sup-', [status(thm)], ['78', '79'])).
% 5.00/5.19  thf('81', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]:
% 5.00/5.19         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 5.00/5.19      inference('sup+', [status(thm)], ['77', '80'])).
% 5.00/5.19  thf('82', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.00/5.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.00/5.19  thf('83', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.00/5.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.00/5.19  thf('84', plain,
% 5.00/5.19      (![X35 : $i, X36 : $i]: (r1_tarski @ X35 @ (k2_xboole_0 @ X35 @ X36))),
% 5.00/5.19      inference('cnf', [status(esa)], [t7_xboole_1])).
% 5.00/5.19  thf('85', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 5.00/5.19      inference('sup+', [status(thm)], ['83', '84'])).
% 5.00/5.19  thf('86', plain,
% 5.00/5.19      (![X43 : $i, X44 : $i]:
% 5.00/5.19         ((r2_hidden @ X43 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X43 @ X44))),
% 5.00/5.19      inference('simplify', [status(thm)], ['20'])).
% 5.00/5.19  thf('87', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]:
% 5.00/5.19         (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.00/5.19      inference('sup-', [status(thm)], ['85', '86'])).
% 5.00/5.19  thf('88', plain,
% 5.00/5.19      (![X48 : $i, X49 : $i]:
% 5.00/5.19         ((m1_subset_1 @ X48 @ X49) | ~ (r2_hidden @ X48 @ X49))),
% 5.00/5.19      inference('clc', [status(thm)], ['23', '24'])).
% 5.00/5.19  thf('89', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]:
% 5.00/5.19         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.00/5.19      inference('sup-', [status(thm)], ['87', '88'])).
% 5.00/5.19  thf('90', plain,
% 5.00/5.19      (![X51 : $i, X52 : $i]:
% 5.00/5.19         (((k3_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))
% 5.00/5.19          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X51)))),
% 5.00/5.19      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.00/5.19  thf('91', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]:
% 5.00/5.19         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 5.00/5.19           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 5.00/5.19      inference('sup-', [status(thm)], ['89', '90'])).
% 5.00/5.19  thf('92', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]:
% 5.00/5.19         ((k3_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X1)
% 5.00/5.19           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 5.00/5.19      inference('sup+', [status(thm)], ['82', '91'])).
% 5.00/5.19  thf('93', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]:
% 5.00/5.19         (r1_tarski @ (k3_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X1) @ X0)),
% 5.00/5.19      inference('demod', [status(thm)], ['81', '92'])).
% 5.00/5.19  thf('94', plain,
% 5.00/5.19      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_2)) @ 
% 5.00/5.19        sk_C_2)),
% 5.00/5.19      inference('sup+', [status(thm)], ['72', '93'])).
% 5.00/5.19  thf('95', plain,
% 5.00/5.19      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_2)) = (sk_C_2))),
% 5.00/5.19      inference('demod', [status(thm)], ['49', '94'])).
% 5.00/5.19  thf('96', plain,
% 5.00/5.19      (((sk_C_2) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 5.00/5.19      inference('demod', [status(thm)], ['28', '95'])).
% 5.00/5.19  thf('97', plain,
% 5.00/5.19      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 5.00/5.19         (k3_subset_1 @ sk_A @ sk_B_1)))
% 5.00/5.19         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 5.00/5.19               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 5.00/5.19      inference('split', [status(esa)], ['5'])).
% 5.00/5.19  thf('98', plain,
% 5.00/5.19      (![X23 : $i, X24 : $i, X25 : $i]:
% 5.00/5.19         (~ (r1_tarski @ X23 @ X24)
% 5.00/5.19          | (r1_tarski @ (k4_xboole_0 @ X25 @ X24) @ (k4_xboole_0 @ X25 @ X23)))),
% 5.00/5.19      inference('cnf', [status(esa)], [t34_xboole_1])).
% 5.00/5.19  thf('99', plain,
% 5.00/5.19      ((![X0 : $i]:
% 5.00/5.19          (r1_tarski @ (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1)) @ 
% 5.00/5.19           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_2))))
% 5.00/5.19         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 5.00/5.19               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 5.00/5.19      inference('sup-', [status(thm)], ['97', '98'])).
% 5.00/5.19  thf('100', plain,
% 5.00/5.19      (((r1_tarski @ (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)) @ 
% 5.00/5.19         sk_C_2))
% 5.00/5.19         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 5.00/5.19               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 5.00/5.19      inference('sup+', [status(thm)], ['96', '99'])).
% 5.00/5.19  thf('101', plain,
% 5.00/5.19      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 5.00/5.19      inference('sup-', [status(thm)], ['10', '11'])).
% 5.00/5.19  thf('102', plain,
% 5.00/5.19      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 5.00/5.19      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.00/5.19  thf('103', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_A)),
% 5.00/5.19      inference('sup+', [status(thm)], ['101', '102'])).
% 5.00/5.19  thf('104', plain,
% 5.00/5.19      (![X43 : $i, X44 : $i]:
% 5.00/5.19         ((r2_hidden @ X43 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X43 @ X44))),
% 5.00/5.19      inference('simplify', [status(thm)], ['20'])).
% 5.00/5.19  thf('105', plain,
% 5.00/5.19      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 5.00/5.19      inference('sup-', [status(thm)], ['103', '104'])).
% 5.00/5.19  thf('106', plain,
% 5.00/5.19      (![X48 : $i, X49 : $i]:
% 5.00/5.19         ((m1_subset_1 @ X48 @ X49) | ~ (r2_hidden @ X48 @ X49))),
% 5.00/5.19      inference('clc', [status(thm)], ['23', '24'])).
% 5.00/5.19  thf('107', plain,
% 5.00/5.19      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 5.00/5.19      inference('sup-', [status(thm)], ['105', '106'])).
% 5.00/5.19  thf('108', plain,
% 5.00/5.19      (![X51 : $i, X52 : $i]:
% 5.00/5.19         (((k3_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))
% 5.00/5.19          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X51)))),
% 5.00/5.19      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.00/5.19  thf('109', plain,
% 5.00/5.19      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1))
% 5.00/5.19         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 5.00/5.19      inference('sup-', [status(thm)], ['107', '108'])).
% 5.00/5.19  thf('110', plain,
% 5.00/5.19      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 5.00/5.19      inference('sup-', [status(thm)], ['10', '11'])).
% 5.00/5.19  thf('111', plain,
% 5.00/5.19      (![X28 : $i, X29 : $i]:
% 5.00/5.19         ((k2_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28))
% 5.00/5.19           = (k2_xboole_0 @ X28 @ X29))),
% 5.00/5.19      inference('cnf', [status(esa)], [t39_xboole_1])).
% 5.00/5.19  thf('112', plain,
% 5.00/5.19      (((k2_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 5.00/5.19         = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 5.00/5.19      inference('sup+', [status(thm)], ['110', '111'])).
% 5.00/5.19  thf('113', plain,
% 5.00/5.19      (![X35 : $i, X36 : $i]: (r1_tarski @ X35 @ (k2_xboole_0 @ X35 @ X36))),
% 5.00/5.19      inference('cnf', [status(esa)], [t7_xboole_1])).
% 5.00/5.19  thf('114', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 5.00/5.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.00/5.19  thf('115', plain,
% 5.00/5.19      (![X48 : $i, X49 : $i]:
% 5.00/5.19         (~ (m1_subset_1 @ X48 @ X49)
% 5.00/5.19          | (r2_hidden @ X48 @ X49)
% 5.00/5.19          | (v1_xboole_0 @ X49))),
% 5.00/5.19      inference('cnf', [status(esa)], [d2_subset_1])).
% 5.00/5.19  thf('116', plain,
% 5.00/5.19      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 5.00/5.19        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 5.00/5.19      inference('sup-', [status(thm)], ['114', '115'])).
% 5.00/5.19  thf('117', plain, (![X53 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X53))),
% 5.00/5.19      inference('cnf', [status(esa)], [fc1_subset_1])).
% 5.00/5.19  thf('118', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 5.00/5.19      inference('clc', [status(thm)], ['116', '117'])).
% 5.00/5.19  thf('119', plain,
% 5.00/5.19      (![X44 : $i, X46 : $i]:
% 5.00/5.19         ((r1_tarski @ X46 @ X44) | ~ (r2_hidden @ X46 @ (k1_zfmisc_1 @ X44)))),
% 5.00/5.19      inference('simplify', [status(thm)], ['34'])).
% 5.00/5.19  thf('120', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 5.00/5.19      inference('sup-', [status(thm)], ['118', '119'])).
% 5.00/5.19  thf('121', plain,
% 5.00/5.19      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.00/5.19         (~ (r1_tarski @ X16 @ X17)
% 5.00/5.19          | ~ (r1_tarski @ X17 @ X18)
% 5.00/5.19          | (r1_tarski @ X16 @ X18))),
% 5.00/5.19      inference('cnf', [status(esa)], [t1_xboole_1])).
% 5.00/5.19  thf('122', plain,
% 5.00/5.19      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 5.00/5.19      inference('sup-', [status(thm)], ['120', '121'])).
% 5.00/5.19  thf('123', plain,
% 5.00/5.19      (![X0 : $i]: (r1_tarski @ sk_B_1 @ (k2_xboole_0 @ sk_A @ X0))),
% 5.00/5.19      inference('sup-', [status(thm)], ['113', '122'])).
% 5.00/5.19  thf('124', plain,
% 5.00/5.19      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.00/5.19         ((r1_tarski @ (k4_xboole_0 @ X30 @ X31) @ X32)
% 5.00/5.19          | ~ (r1_tarski @ X30 @ (k2_xboole_0 @ X31 @ X32)))),
% 5.00/5.19      inference('cnf', [status(esa)], [t43_xboole_1])).
% 5.00/5.19  thf('125', plain,
% 5.00/5.19      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B_1 @ sk_A) @ X0)),
% 5.00/5.19      inference('sup-', [status(thm)], ['123', '124'])).
% 5.00/5.19  thf('126', plain,
% 5.00/5.19      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.00/5.19      inference('sup-', [status(thm)], ['60', '61'])).
% 5.00/5.19  thf('127', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 5.00/5.19      inference('sup-', [status(thm)], ['125', '126'])).
% 5.00/5.19  thf('128', plain,
% 5.00/5.19      (![X28 : $i, X29 : $i]:
% 5.00/5.19         ((k2_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28))
% 5.00/5.19           = (k2_xboole_0 @ X28 @ X29))),
% 5.00/5.19      inference('cnf', [status(esa)], [t39_xboole_1])).
% 5.00/5.19  thf('129', plain,
% 5.00/5.19      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B_1))),
% 5.00/5.19      inference('sup+', [status(thm)], ['127', '128'])).
% 5.00/5.19  thf('130', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.00/5.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.00/5.19  thf('131', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 5.00/5.19      inference('sup+', [status(thm)], ['67', '68'])).
% 5.00/5.19  thf('132', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.00/5.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.00/5.19  thf('133', plain, (((sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 5.00/5.19      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 5.00/5.19  thf('134', plain,
% 5.00/5.19      (((k2_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_A))),
% 5.00/5.19      inference('demod', [status(thm)], ['112', '133'])).
% 5.00/5.19  thf('135', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]:
% 5.00/5.19         (r1_tarski @ (k3_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X1) @ X0)),
% 5.00/5.19      inference('demod', [status(thm)], ['81', '92'])).
% 5.00/5.19  thf('136', plain,
% 5.00/5.19      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)) @ 
% 5.00/5.19        sk_B_1)),
% 5.00/5.19      inference('sup+', [status(thm)], ['134', '135'])).
% 5.00/5.19  thf('137', plain,
% 5.00/5.19      (![X9 : $i, X11 : $i]:
% 5.00/5.19         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 5.00/5.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.00/5.19  thf('138', plain,
% 5.00/5.19      ((~ (r1_tarski @ sk_B_1 @ 
% 5.00/5.19           (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 5.00/5.19        | ((sk_B_1) = (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 5.00/5.19      inference('sup-', [status(thm)], ['136', '137'])).
% 5.00/5.19  thf('139', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 5.00/5.19      inference('sup-', [status(thm)], ['118', '119'])).
% 5.00/5.19  thf('140', plain,
% 5.00/5.19      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 5.00/5.19      inference('sup-', [status(thm)], ['10', '11'])).
% 5.00/5.19  thf('141', plain,
% 5.00/5.19      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 5.00/5.19      inference('sup-', [status(thm)], ['39', '40'])).
% 5.00/5.19  thf('142', plain, ((r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 5.00/5.19      inference('sup+', [status(thm)], ['140', '141'])).
% 5.00/5.19  thf('143', plain,
% 5.00/5.19      (![X40 : $i, X41 : $i, X42 : $i]:
% 5.00/5.19         (~ (r1_tarski @ X40 @ X41)
% 5.00/5.19          | ~ (r1_xboole_0 @ X40 @ X42)
% 5.00/5.19          | (r1_tarski @ X40 @ (k4_xboole_0 @ X41 @ X42)))),
% 5.00/5.19      inference('cnf', [status(esa)], [t86_xboole_1])).
% 5.00/5.19  thf('144', plain,
% 5.00/5.19      (![X0 : $i]:
% 5.00/5.19         ((r1_tarski @ sk_B_1 @ 
% 5.00/5.19           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 5.00/5.19          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 5.00/5.19      inference('sup-', [status(thm)], ['142', '143'])).
% 5.00/5.19  thf('145', plain,
% 5.00/5.19      ((r1_tarski @ sk_B_1 @ 
% 5.00/5.19        (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 5.00/5.19      inference('sup-', [status(thm)], ['139', '144'])).
% 5.00/5.19  thf('146', plain,
% 5.00/5.19      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1))
% 5.00/5.19         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 5.00/5.19      inference('sup-', [status(thm)], ['107', '108'])).
% 5.00/5.19  thf('147', plain,
% 5.00/5.19      ((r1_tarski @ sk_B_1 @ 
% 5.00/5.19        (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 5.00/5.19      inference('demod', [status(thm)], ['145', '146'])).
% 5.00/5.19  thf('148', plain,
% 5.00/5.19      (((sk_B_1) = (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 5.00/5.19      inference('demod', [status(thm)], ['138', '147'])).
% 5.00/5.19  thf('149', plain,
% 5.00/5.19      (((sk_B_1) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 5.00/5.19      inference('demod', [status(thm)], ['109', '148'])).
% 5.00/5.19  thf('150', plain,
% 5.00/5.19      (((r1_tarski @ sk_B_1 @ sk_C_2))
% 5.00/5.19         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 5.00/5.19               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 5.00/5.19      inference('demod', [status(thm)], ['100', '149'])).
% 5.00/5.19  thf('151', plain,
% 5.00/5.19      ((~ (r1_tarski @ sk_B_1 @ sk_C_2)) <= (~ ((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 5.00/5.19      inference('split', [status(esa)], ['0'])).
% 5.00/5.19  thf('152', plain,
% 5.00/5.19      (~
% 5.00/5.19       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 5.00/5.19         (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 5.00/5.19       ((r1_tarski @ sk_B_1 @ sk_C_2))),
% 5.00/5.19      inference('sup-', [status(thm)], ['150', '151'])).
% 5.00/5.19  thf('153', plain, ($false),
% 5.00/5.19      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '152'])).
% 5.00/5.19  
% 5.00/5.19  % SZS output end Refutation
% 5.00/5.19  
% 5.00/5.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
