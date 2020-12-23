%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OHcc1NamaQ

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 146 expanded)
%              Number of leaves         :   42 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  830 (1104 expanded)
%              Number of equality atoms :   78 ( 108 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X42 ) @ ( k2_tarski @ X42 @ X43 ) )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X52 @ X53 ) )
      = ( k3_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['12','15'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('17',plain,(
    ! [X39: $i,X41: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X39 ) @ X41 )
        = ( k1_tarski @ X39 ) )
      | ( r2_hidden @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('22',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = o_0_0_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k10_relat_1 @ X54 @ X55 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X54 ) @ X55 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k10_relat_1 @ X54 @ X55 )
       != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X54 ) @ X55 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('31',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( o_0_0_xboole_0
      = ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','33'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_enumset1 @ X10 @ X10 @ X11 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('36',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X12 @ X12 @ X13 @ X14 )
      = ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k4_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('41',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k5_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k4_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('42',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k6_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(fc7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ~ ( v1_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) )).

thf('43',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ~ ( v1_xboole_0 @ ( k6_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc7_subset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ~ ( v1_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ~ ( v1_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ~ ( v1_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( v1_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf('50',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','49'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('53',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('56',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X37 ) @ X38 )
      | ( r2_hidden @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X54 ) @ X55 )
      | ( ( k10_relat_1 @ X54 @ X55 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('60',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('61',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X54 ) @ X55 )
      | ( ( k10_relat_1 @ X54 @ X55 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['19'])).

thf('64',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = o_0_0_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('69',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != o_0_0_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','54','55','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OHcc1NamaQ
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:17:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 190 iterations in 0.070s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.52  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.20/0.52                                           $i > $i).
% 0.20/0.52  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(t142_funct_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.20/0.52         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ( v1_relat_1 @ B ) =>
% 0.20/0.52          ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.20/0.52            ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t142_funct_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.20/0.52        | (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) | 
% 0.20/0.52       ~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf(t69_enumset1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.52  thf('2', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.52  thf(t19_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.20/0.52       ( k1_tarski @ A ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X42 : $i, X43 : $i]:
% 0.20/0.52         ((k3_xboole_0 @ (k1_tarski @ X42) @ (k2_tarski @ X42 @ X43))
% 0.20/0.52           = (k1_tarski @ X42))),
% 0.20/0.52      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.52           = (k1_tarski @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('5', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.52  thf(t12_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X52 : $i, X53 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X52 @ X53)) = (k3_xboole_0 @ X52 @ X53))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k1_tarski @ (k1_tarski @ X0))) = (k1_tarski @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf(t100_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X6 @ X7)
% 0.20/0.52           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X0 @ X0)
% 0.20/0.52           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.52           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['8', '11'])).
% 0.20/0.52  thf(t92_xboole_1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('13', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.52  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.20/0.52  thf('14', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.52  thf('15', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (o_0_0_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.52           = (o_0_0_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['12', '15'])).
% 0.20/0.52  thf(l33_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.52       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X39 : $i, X41 : $i]:
% 0.20/0.52         (((k4_xboole_0 @ (k1_tarski @ X39) @ X41) = (k1_tarski @ X39))
% 0.20/0.52          | (r2_hidden @ X39 @ X41))),
% 0.20/0.52      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((o_0_0_xboole_0) = (k1_tarski @ X0))
% 0.20/0.52          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.20/0.52        | ~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.20/0.52         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['19'])).
% 0.20/0.52  thf('21', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (o_0_0_xboole_0)))
% 0.20/0.52         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf(t173_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.52         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X54 : $i, X55 : $i]:
% 0.20/0.52         (((k10_relat_1 @ X54 @ X55) != (k1_xboole_0))
% 0.20/0.52          | (r1_xboole_0 @ (k2_relat_1 @ X54) @ X55)
% 0.20/0.52          | ~ (v1_relat_1 @ X54))),
% 0.20/0.52      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.20/0.52  thf('24', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X54 : $i, X55 : $i]:
% 0.20/0.52         (((k10_relat_1 @ X54 @ X55) != (o_0_0_xboole_0))
% 0.20/0.52          | (r1_xboole_0 @ (k2_relat_1 @ X54) @ X55)
% 0.20/0.52          | ~ (v1_relat_1 @ X54))),
% 0.20/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (((((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.20/0.52         | ~ (v1_relat_1 @ sk_B)
% 0.20/0.52         | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.20/0.52         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.52  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (((((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.20/0.52         | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.20/0.52         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))
% 0.20/0.52         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.20/0.52         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf(t3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.52          | ~ (r2_hidden @ X4 @ X5)
% 0.20/0.52          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (~ (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ X0)
% 0.20/0.52           | ~ (r2_hidden @ sk_A @ X0)))
% 0.20/0.52         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.20/0.52         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.52             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '32'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      ((((o_0_0_xboole_0) = (k1_tarski @ sk_A)))
% 0.20/0.52         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.52             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '33'])).
% 0.20/0.52  thf(t70_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         ((k1_enumset1 @ X10 @ X10 @ X11) = (k2_tarski @ X10 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.52  thf('36', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf(t71_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.52         ((k2_enumset1 @ X12 @ X12 @ X13 @ X14)
% 0.20/0.52           = (k1_enumset1 @ X12 @ X13 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.52  thf(t72_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.52         ((k3_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18)
% 0.20/0.52           = (k2_enumset1 @ X15 @ X16 @ X17 @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.20/0.52  thf(t73_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.52     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.20/0.52       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.52         ((k4_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.20/0.52           = (k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.20/0.52  thf(t74_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.52     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.52       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.52         ((k5_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29)
% 0.20/0.52           = (k4_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29))),
% 0.20/0.52      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.20/0.52  thf(t75_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.52     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.52       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.52         ((k6_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.20/0.52           = (k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 0.20/0.52      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.20/0.52  thf(fc7_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.52     ( ~( v1_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, 
% 0.20/0.52         X51 : $i]:
% 0.20/0.52         ~ (v1_xboole_0 @ 
% 0.20/0.52            (k6_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc7_subset_1])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         ~ (v1_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.52         ~ (v1_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '44'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.52         ~ (v1_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['40', '45'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.52         ~ (v1_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['39', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '47'])).
% 0.20/0.52  thf('49', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['37', '48'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      ((~ (v1_xboole_0 @ o_0_0_xboole_0))
% 0.20/0.52         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.20/0.52             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['34', '49'])).
% 0.20/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.52  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.52  thf('52', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.52  thf('53', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.52      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) | 
% 0.20/0.52       ~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['50', '53'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) | 
% 0.20/0.52       (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.20/0.52      inference('split', [status(esa)], ['19'])).
% 0.20/0.52  thf(l27_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X37 : $i, X38 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ (k1_tarski @ X37) @ X38) | (r2_hidden @ X37 @ X38))),
% 0.20/0.52      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.52  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (![X54 : $i, X55 : $i]:
% 0.20/0.52         (~ (r1_xboole_0 @ (k2_relat_1 @ X54) @ X55)
% 0.20/0.52          | ((k10_relat_1 @ X54 @ X55) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_relat_1 @ X54))),
% 0.20/0.52      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.20/0.52  thf('60', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (![X54 : $i, X55 : $i]:
% 0.20/0.52         (~ (r1_xboole_0 @ (k2_relat_1 @ X54) @ X55)
% 0.20/0.52          | ((k10_relat_1 @ X54 @ X55) = (o_0_0_xboole_0))
% 0.20/0.52          | ~ (v1_relat_1 @ X54))),
% 0.20/0.52      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ (k2_relat_1 @ X1))
% 0.20/0.52          | ~ (v1_relat_1 @ X1)
% 0.20/0.52          | ((k10_relat_1 @ X1 @ (k1_tarski @ X0)) = (o_0_0_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['58', '61'])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.20/0.52         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['19'])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (o_0_0_xboole_0))
% 0.20/0.52         | ~ (v1_relat_1 @ sk_B)))
% 0.20/0.52         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.52  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (o_0_0_xboole_0)))
% 0.20/0.52         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0)))
% 0.20/0.52         <= (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('68', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (o_0_0_xboole_0)))
% 0.20/0.52         <= (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.20/0.52         <= (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) & 
% 0.20/0.52             ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['66', '69'])).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) | 
% 0.20/0.52       (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['70'])).
% 0.20/0.52  thf('72', plain, ($false),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['1', '54', '55', '71'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
