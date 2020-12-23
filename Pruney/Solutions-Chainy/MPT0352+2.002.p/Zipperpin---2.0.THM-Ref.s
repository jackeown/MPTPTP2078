%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y8z87l2Ly2

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:07 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 178 expanded)
%              Number of leaves         :   42 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  862 (1450 expanded)
%              Number of equality atoms :   43 (  54 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_tarski @ ( k4_xboole_0 @ X19 @ X18 ) @ ( k4_xboole_0 @ X19 @ X17 ) ) ) ),
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
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ( r1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ sk_B_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('26',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
    = ( k2_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ X49 )
      | ( r2_hidden @ X48 @ X49 )
      | ( v1_xboole_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X53: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('31',plain,(
    r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('32',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X44 @ X43 )
      | ( r1_tarski @ X44 @ X42 )
      | ( X43
       != ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('33',plain,(
    ! [X42: $i,X44: $i] :
      ( ( r1_tarski @ X44 @ X42 )
      | ~ ( r2_hidden @ X44 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['31','33'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('36',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C_2 @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('39',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X32 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_xboole_0 @ X26 @ X27 )
      | ~ ( r1_tarski @ X26 @ X27 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('44',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_xboole_0 @ X33 )
      | ~ ( v1_xboole_0 @ X34 )
      | ( X33 = X34 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('48',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('50',plain,(
    ! [X25: $i] :
      ( r1_xboole_0 @ X25 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('51',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_xboole_0 @ X26 @ X27 )
      | ~ ( r1_tarski @ X26 @ X27 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('55',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_xboole_0 @ X35 @ X36 )
      = ( k5_xboole_0 @ X35 @ ( k4_xboole_0 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X25: $i] :
      ( r1_xboole_0 @ X25 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('59',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('60',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('63',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('65',plain,(
    ! [X24: $i] :
      ( ( k4_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['57','66'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('68',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k2_tarski @ X38 @ X37 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('69',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['48','67','72'])).

thf('74',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
    = sk_A ),
    inference(demod,[status(thm)],['26','73'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('75',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ~ ( r1_tarski @ X28 @ ( k2_xboole_0 @ X29 @ X30 ) )
      | ~ ( r1_xboole_0 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
      | ( r1_tarski @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
      | ~ ( r1_tarski @ sk_B_1 @ sk_A ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ X49 )
      | ( r2_hidden @ X48 @ X49 )
      | ( v1_xboole_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('80',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X53: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('82',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X42: $i,X44: $i] :
      ( ( r1_tarski @ X44 @ X42 )
      | ~ ( r2_hidden @ X44 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('84',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['77','84'])).

thf('86',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y8z87l2Ly2
% 0.16/0.38  % Computer   : n022.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 10:22:11 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 1.72/1.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.72/1.97  % Solved by: fo/fo7.sh
% 1.72/1.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.72/1.97  % done 4016 iterations in 1.465s
% 1.72/1.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.72/1.97  % SZS output start Refutation
% 1.72/1.97  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.72/1.97  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.72/1.97  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.72/1.97  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.72/1.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.72/1.97  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.72/1.97  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.72/1.97  thf(sk_A_type, type, sk_A: $i).
% 1.72/1.97  thf(sk_B_type, type, sk_B: $i > $i).
% 1.72/1.97  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.72/1.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.72/1.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.72/1.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.72/1.97  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.72/1.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.72/1.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.72/1.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.72/1.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.72/1.97  thf(t31_subset_1, conjecture,
% 1.72/1.97    (![A:$i,B:$i]:
% 1.72/1.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.72/1.97       ( ![C:$i]:
% 1.72/1.97         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.72/1.97           ( ( r1_tarski @ B @ C ) <=>
% 1.72/1.97             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.72/1.97  thf(zf_stmt_0, negated_conjecture,
% 1.72/1.97    (~( ![A:$i,B:$i]:
% 1.72/1.97        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.72/1.97          ( ![C:$i]:
% 1.72/1.97            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.72/1.97              ( ( r1_tarski @ B @ C ) <=>
% 1.72/1.97                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 1.72/1.97    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 1.72/1.97  thf('0', plain,
% 1.72/1.97      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.72/1.97           (k3_subset_1 @ sk_A @ sk_B_1))
% 1.72/1.97        | ~ (r1_tarski @ sk_B_1 @ sk_C_2))),
% 1.72/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.97  thf('1', plain,
% 1.72/1.97      (~
% 1.72/1.97       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.72/1.97         (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 1.72/1.97       ~ ((r1_tarski @ sk_B_1 @ sk_C_2))),
% 1.72/1.97      inference('split', [status(esa)], ['0'])).
% 1.72/1.97  thf('2', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.72/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.97  thf(d5_subset_1, axiom,
% 1.72/1.97    (![A:$i,B:$i]:
% 1.72/1.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.72/1.97       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.72/1.97  thf('3', plain,
% 1.72/1.97      (![X51 : $i, X52 : $i]:
% 1.72/1.97         (((k3_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))
% 1.72/1.97          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X51)))),
% 1.72/1.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.72/1.97  thf('4', plain,
% 1.72/1.97      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 1.72/1.97      inference('sup-', [status(thm)], ['2', '3'])).
% 1.72/1.97  thf('5', plain,
% 1.72/1.97      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.72/1.97         (k3_subset_1 @ sk_A @ sk_B_1))
% 1.72/1.97        | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 1.72/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.97  thf('6', plain,
% 1.72/1.97      (((r1_tarski @ sk_B_1 @ sk_C_2)) <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 1.72/1.97      inference('split', [status(esa)], ['5'])).
% 1.72/1.97  thf(t34_xboole_1, axiom,
% 1.72/1.97    (![A:$i,B:$i,C:$i]:
% 1.72/1.97     ( ( r1_tarski @ A @ B ) =>
% 1.72/1.97       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 1.72/1.97  thf('7', plain,
% 1.72/1.97      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.72/1.97         (~ (r1_tarski @ X17 @ X18)
% 1.72/1.97          | (r1_tarski @ (k4_xboole_0 @ X19 @ X18) @ (k4_xboole_0 @ X19 @ X17)))),
% 1.72/1.97      inference('cnf', [status(esa)], [t34_xboole_1])).
% 1.72/1.97  thf('8', plain,
% 1.72/1.97      ((![X0 : $i]:
% 1.72/1.97          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_2) @ 
% 1.72/1.97           (k4_xboole_0 @ X0 @ sk_B_1)))
% 1.72/1.97         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 1.72/1.97      inference('sup-', [status(thm)], ['6', '7'])).
% 1.72/1.97  thf('9', plain,
% 1.72/1.97      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.72/1.97         (k4_xboole_0 @ sk_A @ sk_B_1))) <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 1.72/1.97      inference('sup+', [status(thm)], ['4', '8'])).
% 1.72/1.97  thf('10', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.72/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.97  thf('11', plain,
% 1.72/1.97      (![X51 : $i, X52 : $i]:
% 1.72/1.97         (((k3_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))
% 1.72/1.97          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X51)))),
% 1.72/1.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.72/1.97  thf('12', plain,
% 1.72/1.97      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 1.72/1.97      inference('sup-', [status(thm)], ['10', '11'])).
% 1.72/1.97  thf('13', plain,
% 1.72/1.97      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.72/1.97         (k3_subset_1 @ sk_A @ sk_B_1))) <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 1.72/1.97      inference('demod', [status(thm)], ['9', '12'])).
% 1.72/1.97  thf('14', plain,
% 1.72/1.97      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.72/1.97           (k3_subset_1 @ sk_A @ sk_B_1)))
% 1.72/1.97         <= (~
% 1.72/1.97             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.72/1.97               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 1.72/1.97      inference('split', [status(esa)], ['0'])).
% 1.72/1.97  thf('15', plain,
% 1.72/1.97      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.72/1.97         (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 1.72/1.97       ~ ((r1_tarski @ sk_B_1 @ sk_C_2))),
% 1.72/1.97      inference('sup-', [status(thm)], ['13', '14'])).
% 1.72/1.97  thf('16', plain,
% 1.72/1.97      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.72/1.97         (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 1.72/1.97       ((r1_tarski @ sk_B_1 @ sk_C_2))),
% 1.72/1.97      inference('split', [status(esa)], ['5'])).
% 1.72/1.97  thf('17', plain,
% 1.72/1.97      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.72/1.97         (k3_subset_1 @ sk_A @ sk_B_1)))
% 1.72/1.97         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.72/1.97               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 1.72/1.97      inference('split', [status(esa)], ['5'])).
% 1.72/1.97  thf('18', plain,
% 1.72/1.97      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 1.72/1.97      inference('sup-', [status(thm)], ['10', '11'])).
% 1.72/1.97  thf(t106_xboole_1, axiom,
% 1.72/1.97    (![A:$i,B:$i,C:$i]:
% 1.72/1.97     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.72/1.97       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.72/1.97  thf('19', plain,
% 1.72/1.97      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.72/1.97         ((r1_xboole_0 @ X11 @ X13)
% 1.72/1.97          | ~ (r1_tarski @ X11 @ (k4_xboole_0 @ X12 @ X13)))),
% 1.72/1.97      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.72/1.97  thf('20', plain,
% 1.72/1.97      (![X0 : $i]:
% 1.72/1.97         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 1.72/1.97          | (r1_xboole_0 @ X0 @ sk_B_1))),
% 1.72/1.97      inference('sup-', [status(thm)], ['18', '19'])).
% 1.72/1.97  thf('21', plain,
% 1.72/1.97      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_2) @ sk_B_1))
% 1.72/1.97         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.72/1.97               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 1.72/1.97      inference('sup-', [status(thm)], ['17', '20'])).
% 1.72/1.97  thf(symmetry_r1_xboole_0, axiom,
% 1.72/1.97    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.72/1.97  thf('22', plain,
% 1.72/1.97      (![X2 : $i, X3 : $i]:
% 1.72/1.97         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.72/1.97      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.72/1.97  thf('23', plain,
% 1.72/1.97      (((r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_2)))
% 1.72/1.97         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.72/1.97               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 1.72/1.97      inference('sup-', [status(thm)], ['21', '22'])).
% 1.72/1.97  thf('24', plain,
% 1.72/1.97      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 1.72/1.97      inference('sup-', [status(thm)], ['2', '3'])).
% 1.72/1.97  thf(t39_xboole_1, axiom,
% 1.72/1.97    (![A:$i,B:$i]:
% 1.72/1.97     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.72/1.97  thf('25', plain,
% 1.72/1.97      (![X22 : $i, X23 : $i]:
% 1.72/1.97         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 1.72/1.97           = (k2_xboole_0 @ X22 @ X23))),
% 1.72/1.97      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.72/1.97  thf('26', plain,
% 1.72/1.97      (((k2_xboole_0 @ sk_C_2 @ (k3_subset_1 @ sk_A @ sk_C_2))
% 1.72/1.97         = (k2_xboole_0 @ sk_C_2 @ sk_A))),
% 1.72/1.97      inference('sup+', [status(thm)], ['24', '25'])).
% 1.72/1.97  thf('27', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.72/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.97  thf(d2_subset_1, axiom,
% 1.72/1.97    (![A:$i,B:$i]:
% 1.72/1.97     ( ( ( v1_xboole_0 @ A ) =>
% 1.72/1.97         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.72/1.97       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.72/1.97         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.72/1.97  thf('28', plain,
% 1.72/1.97      (![X48 : $i, X49 : $i]:
% 1.72/1.97         (~ (m1_subset_1 @ X48 @ X49)
% 1.72/1.97          | (r2_hidden @ X48 @ X49)
% 1.72/1.97          | (v1_xboole_0 @ X49))),
% 1.72/1.97      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.72/1.97  thf('29', plain,
% 1.72/1.97      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.72/1.97        | (r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A)))),
% 1.72/1.97      inference('sup-', [status(thm)], ['27', '28'])).
% 1.72/1.97  thf(fc1_subset_1, axiom,
% 1.72/1.97    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.72/1.97  thf('30', plain, (![X53 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X53))),
% 1.72/1.97      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.72/1.97  thf('31', plain, ((r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.72/1.97      inference('clc', [status(thm)], ['29', '30'])).
% 1.72/1.97  thf(d1_zfmisc_1, axiom,
% 1.72/1.97    (![A:$i,B:$i]:
% 1.72/1.97     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.72/1.97       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.72/1.97  thf('32', plain,
% 1.72/1.97      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.72/1.97         (~ (r2_hidden @ X44 @ X43)
% 1.72/1.97          | (r1_tarski @ X44 @ X42)
% 1.72/1.97          | ((X43) != (k1_zfmisc_1 @ X42)))),
% 1.72/1.97      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.72/1.97  thf('33', plain,
% 1.72/1.97      (![X42 : $i, X44 : $i]:
% 1.72/1.97         ((r1_tarski @ X44 @ X42) | ~ (r2_hidden @ X44 @ (k1_zfmisc_1 @ X42)))),
% 1.72/1.97      inference('simplify', [status(thm)], ['32'])).
% 1.72/1.97  thf('34', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 1.72/1.97      inference('sup-', [status(thm)], ['31', '33'])).
% 1.72/1.97  thf(t36_xboole_1, axiom,
% 1.72/1.97    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.72/1.97  thf('35', plain,
% 1.72/1.97      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 1.72/1.97      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.72/1.97  thf(t1_xboole_1, axiom,
% 1.72/1.97    (![A:$i,B:$i,C:$i]:
% 1.72/1.97     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.72/1.97       ( r1_tarski @ A @ C ) ))).
% 1.72/1.97  thf('36', plain,
% 1.72/1.97      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.72/1.97         (~ (r1_tarski @ X14 @ X15)
% 1.72/1.97          | ~ (r1_tarski @ X15 @ X16)
% 1.72/1.97          | (r1_tarski @ X14 @ X16))),
% 1.72/1.97      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.72/1.97  thf('37', plain,
% 1.72/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.97         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 1.72/1.97      inference('sup-', [status(thm)], ['35', '36'])).
% 1.72/1.97  thf('38', plain,
% 1.72/1.97      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C_2 @ X0) @ sk_A)),
% 1.72/1.97      inference('sup-', [status(thm)], ['34', '37'])).
% 1.72/1.97  thf(t79_xboole_1, axiom,
% 1.72/1.97    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.72/1.97  thf('39', plain,
% 1.72/1.97      (![X31 : $i, X32 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X32)),
% 1.72/1.97      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.72/1.97  thf(t69_xboole_1, axiom,
% 1.72/1.97    (![A:$i,B:$i]:
% 1.72/1.97     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.72/1.97       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 1.72/1.97  thf('40', plain,
% 1.72/1.97      (![X26 : $i, X27 : $i]:
% 1.72/1.97         (~ (r1_xboole_0 @ X26 @ X27)
% 1.72/1.97          | ~ (r1_tarski @ X26 @ X27)
% 1.72/1.97          | (v1_xboole_0 @ X26))),
% 1.72/1.97      inference('cnf', [status(esa)], [t69_xboole_1])).
% 1.72/1.97  thf('41', plain,
% 1.72/1.97      (![X0 : $i, X1 : $i]:
% 1.72/1.97         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 1.72/1.97          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.72/1.97      inference('sup-', [status(thm)], ['39', '40'])).
% 1.72/1.97  thf('42', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_C_2 @ sk_A))),
% 1.72/1.97      inference('sup-', [status(thm)], ['38', '41'])).
% 1.72/1.97  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.72/1.97  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.72/1.97      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.72/1.97  thf(t8_boole, axiom,
% 1.72/1.97    (![A:$i,B:$i]:
% 1.72/1.97     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.72/1.97  thf('44', plain,
% 1.72/1.97      (![X33 : $i, X34 : $i]:
% 1.72/1.97         (~ (v1_xboole_0 @ X33) | ~ (v1_xboole_0 @ X34) | ((X33) = (X34)))),
% 1.72/1.97      inference('cnf', [status(esa)], [t8_boole])).
% 1.72/1.97  thf('45', plain,
% 1.72/1.97      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.72/1.97      inference('sup-', [status(thm)], ['43', '44'])).
% 1.72/1.97  thf('46', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_C_2 @ sk_A))),
% 1.72/1.97      inference('sup-', [status(thm)], ['42', '45'])).
% 1.72/1.97  thf('47', plain,
% 1.72/1.97      (![X22 : $i, X23 : $i]:
% 1.72/1.97         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 1.72/1.97           = (k2_xboole_0 @ X22 @ X23))),
% 1.72/1.97      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.72/1.97  thf('48', plain,
% 1.72/1.97      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_C_2))),
% 1.72/1.97      inference('sup+', [status(thm)], ['46', '47'])).
% 1.72/1.97  thf('49', plain,
% 1.72/1.97      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 1.72/1.97      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.72/1.97  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.72/1.97  thf('50', plain, (![X25 : $i]: (r1_xboole_0 @ X25 @ k1_xboole_0)),
% 1.72/1.97      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.72/1.97  thf('51', plain,
% 1.72/1.97      (![X26 : $i, X27 : $i]:
% 1.72/1.97         (~ (r1_xboole_0 @ X26 @ X27)
% 1.72/1.97          | ~ (r1_tarski @ X26 @ X27)
% 1.72/1.97          | (v1_xboole_0 @ X26))),
% 1.72/1.97      inference('cnf', [status(esa)], [t69_xboole_1])).
% 1.72/1.97  thf('52', plain,
% 1.72/1.97      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 1.72/1.97      inference('sup-', [status(thm)], ['50', '51'])).
% 1.72/1.97  thf('53', plain,
% 1.72/1.97      (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.72/1.97      inference('sup-', [status(thm)], ['49', '52'])).
% 1.72/1.97  thf('54', plain,
% 1.72/1.97      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.72/1.97      inference('sup-', [status(thm)], ['43', '44'])).
% 1.72/1.97  thf('55', plain,
% 1.72/1.97      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.72/1.97      inference('sup-', [status(thm)], ['53', '54'])).
% 1.72/1.97  thf(t98_xboole_1, axiom,
% 1.72/1.97    (![A:$i,B:$i]:
% 1.72/1.97     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.72/1.97  thf('56', plain,
% 1.72/1.97      (![X35 : $i, X36 : $i]:
% 1.72/1.97         ((k2_xboole_0 @ X35 @ X36)
% 1.72/1.97           = (k5_xboole_0 @ X35 @ (k4_xboole_0 @ X36 @ X35)))),
% 1.72/1.97      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.72/1.97  thf('57', plain,
% 1.72/1.97      (![X0 : $i]:
% 1.72/1.97         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.72/1.97      inference('sup+', [status(thm)], ['55', '56'])).
% 1.72/1.97  thf('58', plain, (![X25 : $i]: (r1_xboole_0 @ X25 @ k1_xboole_0)),
% 1.72/1.97      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.72/1.97  thf(t7_xboole_0, axiom,
% 1.72/1.97    (![A:$i]:
% 1.72/1.97     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.72/1.97          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.72/1.97  thf('59', plain,
% 1.72/1.97      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 1.72/1.97      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.72/1.97  thf(t4_xboole_0, axiom,
% 1.72/1.97    (![A:$i,B:$i]:
% 1.72/1.97     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.72/1.97            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.72/1.97       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.72/1.97            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.72/1.97  thf('60', plain,
% 1.72/1.97      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.72/1.97         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 1.72/1.97          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.72/1.97      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.72/1.97  thf('61', plain,
% 1.72/1.97      (![X0 : $i, X1 : $i]:
% 1.72/1.97         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.72/1.97      inference('sup-', [status(thm)], ['59', '60'])).
% 1.72/1.97  thf('62', plain,
% 1.72/1.97      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.72/1.97      inference('sup-', [status(thm)], ['58', '61'])).
% 1.72/1.97  thf(t100_xboole_1, axiom,
% 1.72/1.97    (![A:$i,B:$i]:
% 1.72/1.97     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.72/1.97  thf('63', plain,
% 1.72/1.97      (![X9 : $i, X10 : $i]:
% 1.72/1.97         ((k4_xboole_0 @ X9 @ X10)
% 1.72/1.97           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 1.72/1.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.72/1.97  thf('64', plain,
% 1.72/1.97      (![X0 : $i]:
% 1.72/1.97         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.72/1.97      inference('sup+', [status(thm)], ['62', '63'])).
% 1.72/1.97  thf(t3_boole, axiom,
% 1.72/1.97    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.72/1.97  thf('65', plain, (![X24 : $i]: ((k4_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 1.72/1.97      inference('cnf', [status(esa)], [t3_boole])).
% 1.72/1.97  thf('66', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.72/1.97      inference('sup+', [status(thm)], ['64', '65'])).
% 1.72/1.97  thf('67', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.72/1.97      inference('demod', [status(thm)], ['57', '66'])).
% 1.72/1.97  thf(commutativity_k2_tarski, axiom,
% 1.72/1.97    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.72/1.97  thf('68', plain,
% 1.72/1.97      (![X37 : $i, X38 : $i]:
% 1.72/1.97         ((k2_tarski @ X38 @ X37) = (k2_tarski @ X37 @ X38))),
% 1.72/1.97      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.72/1.97  thf(l51_zfmisc_1, axiom,
% 1.72/1.97    (![A:$i,B:$i]:
% 1.72/1.97     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.72/1.97  thf('69', plain,
% 1.72/1.97      (![X46 : $i, X47 : $i]:
% 1.72/1.97         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 1.72/1.97      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.72/1.97  thf('70', plain,
% 1.72/1.97      (![X0 : $i, X1 : $i]:
% 1.72/1.97         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.72/1.97      inference('sup+', [status(thm)], ['68', '69'])).
% 1.72/1.97  thf('71', plain,
% 1.72/1.97      (![X46 : $i, X47 : $i]:
% 1.72/1.97         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 1.72/1.97      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.72/1.97  thf('72', plain,
% 1.72/1.97      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.72/1.97      inference('sup+', [status(thm)], ['70', '71'])).
% 1.72/1.97  thf('73', plain, (((sk_A) = (k2_xboole_0 @ sk_C_2 @ sk_A))),
% 1.72/1.97      inference('demod', [status(thm)], ['48', '67', '72'])).
% 1.72/1.97  thf('74', plain,
% 1.72/1.97      (((k2_xboole_0 @ sk_C_2 @ (k3_subset_1 @ sk_A @ sk_C_2)) = (sk_A))),
% 1.72/1.97      inference('demod', [status(thm)], ['26', '73'])).
% 1.72/1.97  thf(t73_xboole_1, axiom,
% 1.72/1.97    (![A:$i,B:$i,C:$i]:
% 1.72/1.97     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 1.72/1.97       ( r1_tarski @ A @ B ) ))).
% 1.72/1.97  thf('75', plain,
% 1.72/1.97      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.72/1.97         ((r1_tarski @ X28 @ X29)
% 1.72/1.97          | ~ (r1_tarski @ X28 @ (k2_xboole_0 @ X29 @ X30))
% 1.72/1.97          | ~ (r1_xboole_0 @ X28 @ X30))),
% 1.72/1.97      inference('cnf', [status(esa)], [t73_xboole_1])).
% 1.72/1.97  thf('76', plain,
% 1.72/1.97      (![X0 : $i]:
% 1.72/1.97         (~ (r1_tarski @ X0 @ sk_A)
% 1.72/1.97          | ~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_2))
% 1.72/1.97          | (r1_tarski @ X0 @ sk_C_2))),
% 1.72/1.97      inference('sup-', [status(thm)], ['74', '75'])).
% 1.72/1.97  thf('77', plain,
% 1.72/1.97      ((((r1_tarski @ sk_B_1 @ sk_C_2) | ~ (r1_tarski @ sk_B_1 @ sk_A)))
% 1.72/1.97         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.72/1.97               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 1.72/1.97      inference('sup-', [status(thm)], ['23', '76'])).
% 1.72/1.97  thf('78', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.72/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.97  thf('79', plain,
% 1.72/1.97      (![X48 : $i, X49 : $i]:
% 1.72/1.97         (~ (m1_subset_1 @ X48 @ X49)
% 1.72/1.97          | (r2_hidden @ X48 @ X49)
% 1.72/1.97          | (v1_xboole_0 @ X49))),
% 1.72/1.97      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.72/1.97  thf('80', plain,
% 1.72/1.97      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.72/1.97        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.72/1.97      inference('sup-', [status(thm)], ['78', '79'])).
% 1.72/1.97  thf('81', plain, (![X53 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X53))),
% 1.72/1.97      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.72/1.97  thf('82', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.72/1.97      inference('clc', [status(thm)], ['80', '81'])).
% 1.72/1.97  thf('83', plain,
% 1.72/1.97      (![X42 : $i, X44 : $i]:
% 1.72/1.97         ((r1_tarski @ X44 @ X42) | ~ (r2_hidden @ X44 @ (k1_zfmisc_1 @ X42)))),
% 1.72/1.97      inference('simplify', [status(thm)], ['32'])).
% 1.72/1.97  thf('84', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 1.72/1.97      inference('sup-', [status(thm)], ['82', '83'])).
% 1.72/1.97  thf('85', plain,
% 1.72/1.97      (((r1_tarski @ sk_B_1 @ sk_C_2))
% 1.72/1.97         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.72/1.97               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 1.72/1.97      inference('demod', [status(thm)], ['77', '84'])).
% 1.72/1.97  thf('86', plain,
% 1.72/1.97      ((~ (r1_tarski @ sk_B_1 @ sk_C_2)) <= (~ ((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 1.72/1.97      inference('split', [status(esa)], ['0'])).
% 1.72/1.97  thf('87', plain,
% 1.72/1.97      (~
% 1.72/1.97       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.72/1.97         (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 1.72/1.97       ((r1_tarski @ sk_B_1 @ sk_C_2))),
% 1.72/1.97      inference('sup-', [status(thm)], ['85', '86'])).
% 1.72/1.97  thf('88', plain, ($false),
% 1.72/1.97      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '87'])).
% 1.72/1.97  
% 1.72/1.97  % SZS output end Refutation
% 1.72/1.97  
% 1.83/1.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
