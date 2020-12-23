%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1rQfNjki4U

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 215 expanded)
%              Number of leaves         :   28 (  67 expanded)
%              Depth                    :   19
%              Number of atoms          :  763 (2233 expanded)
%              Number of equality atoms :   63 ( 207 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t142_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
        <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_1])).

thf('0',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k10_relat_1 @ X22 @ X23 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('4',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('9',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['11'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('13',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('14',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t174_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( r1_tarski @ X24 @ ( k2_relat_1 @ X25 ) )
      | ( ( k10_relat_1 @ X25 @ X24 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t174_relat_1])).

thf('16',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( ( k3_xboole_0 @ X16 @ ( k1_tarski @ X15 ) )
       != ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t51_zfmisc_1])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
         != ( k1_tarski @ sk_A ) )
        | ( r2_hidden @ sk_A @ X0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('24',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r2_hidden @ sk_A @ X0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_A @ X0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ~ ( r2_hidden @ C @ A )
            & ( r2_hidden @ C @ B ) )
        & ~ ( ~ ( r2_hidden @ C @ B )
            & ( r2_hidden @ C @ A ) )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( r2_hidden @ C @ A )
        & ~ ( r2_hidden @ C @ B ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( r2_hidden @ C @ B )
        & ~ ( r2_hidden @ C @ A ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ A @ B )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X8 @ X9 )
      | ( zip_tseitin_0 @ X10 @ X9 @ X8 )
      | ( zip_tseitin_1 @ X10 @ X9 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('28',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_1 @ sk_A @ X0 @ X1 )
        | ( zip_tseitin_0 @ sk_A @ X0 @ X1 )
        | ~ ( r1_xboole_0 @ X1 @ X0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( zip_tseitin_0 @ sk_A @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ( zip_tseitin_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','28'])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('31',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('32',plain,
    ( ( ( zip_tseitin_0 @ sk_A @ ( k2_relat_1 @ sk_B ) @ k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ k1_xboole_0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( zip_tseitin_1 @ X5 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,
    ( ( ( zip_tseitin_0 @ sk_A @ ( k2_relat_1 @ sk_B ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['11'])).

thf('36',plain,
    ( ( zip_tseitin_0 @ sk_A @ ( k2_relat_1 @ sk_B ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_A @ X0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('40',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['11'])).

thf(t56_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X17 ) @ X18 )
      | ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t56_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X22 ) @ X23 )
      | ( ( k10_relat_1 @ X22 @ X23 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','40','41','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1rQfNjki4U
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 61 iterations in 0.028s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(t142_funct_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.20/0.51         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ( v1_relat_1 @ B ) =>
% 0.20/0.51          ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.20/0.51            ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t142_funct_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.20/0.51        | ~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.20/0.51       ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.20/0.51         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf(t173_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.51         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X22 : $i, X23 : $i]:
% 0.20/0.51         (((k10_relat_1 @ X22 @ X23) != (k1_xboole_0))
% 0.20/0.51          | (r1_xboole_0 @ (k2_relat_1 @ X22) @ X23)
% 0.20/0.51          | ~ (v1_relat_1 @ X22))),
% 0.20/0.51      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.51         | ~ (v1_relat_1 @ sk_B)
% 0.20/0.51         | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.20/0.51         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('5', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.51         | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.20/0.51         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))
% 0.20/0.51         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.51  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_B)))
% 0.20/0.51         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.20/0.51         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.20/0.51        | (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['11'])).
% 0.20/0.51  thf(l1_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X12 : $i, X14 : $i]:
% 0.20/0.51         ((r1_tarski @ (k1_tarski @ X12) @ X14) | ~ (r2_hidden @ X12 @ X14))),
% 0.20/0.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (((r1_tarski @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_B)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf(t174_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.20/0.51            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i]:
% 0.20/0.51         (((X24) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X25)
% 0.20/0.51          | ~ (r1_tarski @ X24 @ (k2_relat_1 @ X25))
% 0.20/0.51          | ((k10_relat_1 @ X25 @ X24) != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t174_relat_1])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.20/0.51         | ~ (v1_relat_1 @ sk_B)
% 0.20/0.51         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.20/0.51         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.51         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.51             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.51             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.51  thf(t51_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.20/0.51       ( r2_hidden @ B @ A ) ))).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         ((r2_hidden @ X15 @ X16)
% 0.20/0.51          | ((k3_xboole_0 @ X16 @ (k1_tarski @ X15)) != (k1_tarski @ X15)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t51_zfmisc_1])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (((k3_xboole_0 @ X0 @ k1_xboole_0) != (k1_tarski @ sk_A))
% 0.20/0.51           | (r2_hidden @ sk_A @ X0)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.51             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf(t2_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.51             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ sk_A @ X0)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.51             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((![X0 : $i]: (r2_hidden @ sk_A @ X0))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.51             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.51  thf(t5_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ~( ( ~( ( ~( r2_hidden @ C @ A ) ) & ( r2_hidden @ C @ B ) ) ) & 
% 0.20/0.51          ( ~( ( ~( r2_hidden @ C @ B ) ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.51          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ B ) ) ))).
% 0.20/0.51  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_2, axiom,
% 0.20/0.51    (![C:$i,B:$i,A:$i]:
% 0.20/0.51     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.51       ( ( r2_hidden @ C @ A ) & ( ~( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_4, axiom,
% 0.20/0.51    (![C:$i,B:$i,A:$i]:
% 0.20/0.51     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.20/0.51       ( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_5, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ~( ( r1_xboole_0 @ A @ B ) & 
% 0.20/0.51          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & 
% 0.20/0.51          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.51          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (r1_xboole_0 @ X8 @ X9)
% 0.20/0.51          | (zip_tseitin_0 @ X10 @ X9 @ X8)
% 0.20/0.51          | (zip_tseitin_1 @ X10 @ X9 @ X8)
% 0.20/0.51          | ~ (r2_hidden @ X10 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((![X0 : $i, X1 : $i]:
% 0.20/0.51          ((zip_tseitin_1 @ sk_A @ X0 @ X1)
% 0.20/0.51           | (zip_tseitin_0 @ sk_A @ X0 @ X1)
% 0.20/0.51           | ~ (r1_xboole_0 @ X1 @ X0)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.51             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((((zip_tseitin_0 @ sk_A @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A))
% 0.20/0.51         | (zip_tseitin_1 @ sk_A @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.51             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.51             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.51             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((((zip_tseitin_0 @ sk_A @ (k2_relat_1 @ sk_B) @ k1_xboole_0)
% 0.20/0.51         | (zip_tseitin_1 @ sk_A @ (k2_relat_1 @ sk_B) @ k1_xboole_0)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.51             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X5 @ X7) | ~ (zip_tseitin_1 @ X5 @ X7 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((((zip_tseitin_0 @ sk_A @ (k2_relat_1 @ sk_B) @ k1_xboole_0)
% 0.20/0.51         | ~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.51             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['11'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (((zip_tseitin_0 @ sk_A @ (k2_relat_1 @ sk_B) @ k1_xboole_0))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.51             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X2 @ X4) | ~ (zip_tseitin_0 @ X2 @ X3 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ k1_xboole_0))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.51             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((![X0 : $i]: (r2_hidden @ sk_A @ X0))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.51             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.20/0.51       ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.20/0.51       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['11'])).
% 0.20/0.51  thf(t56_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ (k1_tarski @ X17) @ X18) | (r2_hidden @ X17 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t56_zfmisc_1])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (![X22 : $i, X23 : $i]:
% 0.20/0.51         (~ (r1_xboole_0 @ (k2_relat_1 @ X22) @ X23)
% 0.20/0.51          | ((k10_relat_1 @ X22 @ X23) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X22))),
% 0.20/0.51      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ X0 @ (k2_relat_1 @ X1))
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ((k10_relat_1 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.20/0.51         | ~ (v1_relat_1 @ sk_B)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.51  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0)))
% 0.20/0.51         <= (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['11'])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.51         <= (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) & 
% 0.20/0.51             ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.20/0.51       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.51  thf('54', plain, ($false),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['1', '40', '41', '53'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
