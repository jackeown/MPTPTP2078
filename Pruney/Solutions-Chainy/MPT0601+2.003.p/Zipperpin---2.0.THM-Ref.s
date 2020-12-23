%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rJmxHRJLSm

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 254 expanded)
%              Number of leaves         :   28 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          :  694 (2009 expanded)
%              Number of equality atoms :   65 ( 202 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X25: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 )
      | ~ ( r1_tarski @ X26 @ ( k1_relat_1 @ X27 ) )
      | ( ( k9_relat_1 @ X27 @ X26 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('12',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['11'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21
        = ( k1_relat_1 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X21 @ X18 ) @ ( sk_D_1 @ X21 @ X18 ) ) @ X18 )
      | ( r2_hidden @ ( sk_C @ X21 @ X18 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 )
      | ( r2_hidden @ X16 @ X19 )
      | ( X19
       != ( k1_relat_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ ( k1_relat_1 @ X18 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['11'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['19','23'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('25',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k11_relat_1 @ X29 @ X30 ) )
      | ( r2_hidden @ ( k4_tarski @ X30 @ X28 ) @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ ( k1_relat_1 @ X18 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('35',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( r2_hidden @ ( k4_tarski @ X20 @ ( sk_D_2 @ X20 @ X18 ) ) @ X18 )
      | ( X19
       != ( k1_relat_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('36',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X20 @ ( sk_D_2 @ X20 @ X18 ) ) @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_2 @ sk_A @ sk_B ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X30 @ X28 ) @ X29 )
      | ( r2_hidden @ X28 @ ( k11_relat_1 @ X29 @ X30 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('39',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B ) @ X0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('45',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X11 ) @ X13 )
      | ~ ( r2_hidden @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('46',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k1_tarski @ ( sk_D_2 @ sk_A @ sk_B ) ) @ X0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['11'])).

thf('48',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 )
      | ~ ( r1_tarski @ X26 @ ( k1_relat_1 @ X27 ) )
      | ( ( k9_relat_1 @ X27 @ X26 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X25: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','9'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( k1_tarski @ ( sk_D_2 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('55',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('56',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ X15 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('60',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['32','58','59'])).

thf('61',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['30','60'])).

thf('62',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('66',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['32','58'])).

thf('67',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rJmxHRJLSm
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.55  % Solved by: fo/fo7.sh
% 0.19/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.55  % done 267 iterations in 0.132s
% 0.19/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.55  % SZS output start Refutation
% 0.19/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.55  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.19/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.55  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.19/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.55  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.19/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.55  thf(t150_relat_1, axiom,
% 0.19/0.55    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.55  thf('0', plain,
% 0.19/0.55      (![X25 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X25) = (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.19/0.55  thf(d10_xboole_0, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.55  thf('1', plain,
% 0.19/0.55      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.19/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.55  thf('2', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.19/0.55      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.55  thf(t152_relat_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( v1_relat_1 @ B ) =>
% 0.19/0.55       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.55            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.19/0.55            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.55  thf('3', plain,
% 0.19/0.55      (![X26 : $i, X27 : $i]:
% 0.19/0.55         (((X26) = (k1_xboole_0))
% 0.19/0.55          | ~ (v1_relat_1 @ X27)
% 0.19/0.55          | ~ (r1_tarski @ X26 @ (k1_relat_1 @ X27))
% 0.19/0.55          | ((k9_relat_1 @ X27 @ X26) != (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t152_relat_1])).
% 0.19/0.55  thf('4', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) != (k1_xboole_0))
% 0.19/0.55          | ~ (v1_relat_1 @ X0)
% 0.19/0.55          | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.55  thf('5', plain,
% 0.19/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.55        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.19/0.55        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['0', '4'])).
% 0.19/0.55  thf(t205_relat_1, conjecture,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( v1_relat_1 @ B ) =>
% 0.19/0.55       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.19/0.55         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.19/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.55    (~( ![A:$i,B:$i]:
% 0.19/0.55        ( ( v1_relat_1 @ B ) =>
% 0.19/0.55          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.19/0.55            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.55    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.19/0.55  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(t2_boole, axiom,
% 0.19/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.55  thf('7', plain,
% 0.19/0.55      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.55  thf(fc1_relat_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.55  thf('8', plain,
% 0.19/0.55      (![X23 : $i, X24 : $i]:
% 0.19/0.55         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k3_xboole_0 @ X23 @ X24)))),
% 0.19/0.55      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.19/0.55  thf('9', plain,
% 0.19/0.55      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ X0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.55  thf('10', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.55      inference('sup-', [status(thm)], ['6', '9'])).
% 0.19/0.55  thf('11', plain,
% 0.19/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.55        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['5', '10'])).
% 0.19/0.55  thf('12', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.55  thf(d4_relat_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.19/0.55       ( ![C:$i]:
% 0.19/0.55         ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.55           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.19/0.55  thf('13', plain,
% 0.19/0.55      (![X18 : $i, X21 : $i]:
% 0.19/0.55         (((X21) = (k1_relat_1 @ X18))
% 0.19/0.55          | (r2_hidden @ 
% 0.19/0.55             (k4_tarski @ (sk_C @ X21 @ X18) @ (sk_D_1 @ X21 @ X18)) @ X18)
% 0.19/0.55          | (r2_hidden @ (sk_C @ X21 @ X18) @ X21))),
% 0.19/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.19/0.55  thf('14', plain,
% 0.19/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.55         (~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X18)
% 0.19/0.55          | (r2_hidden @ X16 @ X19)
% 0.19/0.55          | ((X19) != (k1_relat_1 @ X18)))),
% 0.19/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.19/0.55  thf('15', plain,
% 0.19/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.55         ((r2_hidden @ X16 @ (k1_relat_1 @ X18))
% 0.19/0.55          | ~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X18))),
% 0.19/0.55      inference('simplify', [status(thm)], ['14'])).
% 0.19/0.55  thf('16', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.19/0.55          | ((X1) = (k1_relat_1 @ X0))
% 0.19/0.55          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['13', '15'])).
% 0.19/0.55  thf('17', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.19/0.55          | ((X0) = (k1_relat_1 @ k1_xboole_0))
% 0.19/0.55          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['12', '16'])).
% 0.19/0.55  thf('18', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.55  thf('19', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.19/0.55          | ((X0) = (k1_xboole_0))
% 0.19/0.55          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.19/0.55      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.55  thf('20', plain,
% 0.19/0.55      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.55  thf(d4_xboole_0, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.19/0.55       ( ![D:$i]:
% 0.19/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.55           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.19/0.55  thf('21', plain,
% 0.19/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.55          | (r2_hidden @ X4 @ X1)
% 0.19/0.55          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.19/0.55  thf('22', plain,
% 0.19/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.55         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.55  thf('23', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['20', '22'])).
% 0.19/0.55  thf('24', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.55      inference('clc', [status(thm)], ['19', '23'])).
% 0.19/0.55  thf(t204_relat_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( v1_relat_1 @ C ) =>
% 0.19/0.55       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.19/0.55         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.19/0.55  thf('25', plain,
% 0.19/0.55      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X28 @ (k11_relat_1 @ X29 @ X30))
% 0.19/0.55          | (r2_hidden @ (k4_tarski @ X30 @ X28) @ X29)
% 0.19/0.55          | ~ (v1_relat_1 @ X29))),
% 0.19/0.55      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.19/0.55  thf('26', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.19/0.55          | ~ (v1_relat_1 @ X1)
% 0.19/0.55          | (r2_hidden @ 
% 0.19/0.55             (k4_tarski @ X0 @ (sk_C @ (k11_relat_1 @ X1 @ X0) @ k1_xboole_0)) @ 
% 0.19/0.55             X1))),
% 0.19/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.55  thf('27', plain,
% 0.19/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.55         ((r2_hidden @ X16 @ (k1_relat_1 @ X18))
% 0.19/0.55          | ~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X18))),
% 0.19/0.55      inference('simplify', [status(thm)], ['14'])).
% 0.19/0.55  thf('28', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (~ (v1_relat_1 @ X0)
% 0.19/0.55          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.19/0.55          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.55  thf('29', plain,
% 0.19/0.55      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.19/0.55        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('30', plain,
% 0.19/0.55      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.19/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.55      inference('split', [status(esa)], ['29'])).
% 0.19/0.55  thf('31', plain,
% 0.19/0.55      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.19/0.55        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('32', plain,
% 0.19/0.55      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.55       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.55      inference('split', [status(esa)], ['31'])).
% 0.19/0.55  thf('33', plain,
% 0.19/0.55      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.19/0.55         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('split', [status(esa)], ['29'])).
% 0.19/0.55  thf('34', plain,
% 0.19/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.19/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.55      inference('split', [status(esa)], ['31'])).
% 0.19/0.55  thf('35', plain,
% 0.19/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X20 @ X19)
% 0.19/0.55          | (r2_hidden @ (k4_tarski @ X20 @ (sk_D_2 @ X20 @ X18)) @ X18)
% 0.19/0.55          | ((X19) != (k1_relat_1 @ X18)))),
% 0.19/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.19/0.55  thf('36', plain,
% 0.19/0.55      (![X18 : $i, X20 : $i]:
% 0.19/0.55         ((r2_hidden @ (k4_tarski @ X20 @ (sk_D_2 @ X20 @ X18)) @ X18)
% 0.19/0.55          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X18)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['35'])).
% 0.19/0.55  thf('37', plain,
% 0.19/0.55      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_2 @ sk_A @ sk_B)) @ sk_B))
% 0.19/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['34', '36'])).
% 0.19/0.55  thf('38', plain,
% 0.19/0.55      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.55         (~ (r2_hidden @ (k4_tarski @ X30 @ X28) @ X29)
% 0.19/0.55          | (r2_hidden @ X28 @ (k11_relat_1 @ X29 @ X30))
% 0.19/0.55          | ~ (v1_relat_1 @ X29))),
% 0.19/0.55      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.19/0.55  thf('39', plain,
% 0.19/0.55      (((~ (v1_relat_1 @ sk_B)
% 0.19/0.55         | (r2_hidden @ (sk_D_2 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A))))
% 0.19/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.55  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('41', plain,
% 0.19/0.55      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A)))
% 0.19/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.55      inference('demod', [status(thm)], ['39', '40'])).
% 0.19/0.55  thf('42', plain,
% 0.19/0.55      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_B) @ k1_xboole_0))
% 0.19/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.19/0.55             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('sup+', [status(thm)], ['33', '41'])).
% 0.19/0.55  thf('43', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['20', '22'])).
% 0.19/0.55  thf('44', plain,
% 0.19/0.55      ((![X0 : $i]: (r2_hidden @ (sk_D_2 @ sk_A @ sk_B) @ X0))
% 0.19/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.19/0.55             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.19/0.55  thf(l1_zfmisc_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.19/0.55  thf('45', plain,
% 0.19/0.55      (![X11 : $i, X13 : $i]:
% 0.19/0.55         ((r1_tarski @ (k1_tarski @ X11) @ X13) | ~ (r2_hidden @ X11 @ X13))),
% 0.19/0.55      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.19/0.55  thf('46', plain,
% 0.19/0.55      ((![X0 : $i]: (r1_tarski @ (k1_tarski @ (sk_D_2 @ sk_A @ sk_B)) @ X0))
% 0.19/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.19/0.55             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.55  thf('47', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.55  thf('48', plain,
% 0.19/0.55      (![X26 : $i, X27 : $i]:
% 0.19/0.55         (((X26) = (k1_xboole_0))
% 0.19/0.55          | ~ (v1_relat_1 @ X27)
% 0.19/0.55          | ~ (r1_tarski @ X26 @ (k1_relat_1 @ X27))
% 0.19/0.55          | ((k9_relat_1 @ X27 @ X26) != (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t152_relat_1])).
% 0.19/0.55  thf('49', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.19/0.55          | ((k9_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.19/0.55          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.55          | ((X0) = (k1_xboole_0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.55  thf('50', plain,
% 0.19/0.55      (![X25 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X25) = (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.19/0.55  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.55      inference('sup-', [status(thm)], ['6', '9'])).
% 0.19/0.55  thf('52', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.19/0.55          | ((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.55          | ((X0) = (k1_xboole_0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.19/0.55  thf('53', plain,
% 0.19/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.19/0.55      inference('simplify', [status(thm)], ['52'])).
% 0.19/0.55  thf('54', plain,
% 0.19/0.55      ((((k1_tarski @ (sk_D_2 @ sk_A @ sk_B)) = (k1_xboole_0)))
% 0.19/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.19/0.55             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['46', '53'])).
% 0.19/0.55  thf(idempotence_k2_xboole_0, axiom,
% 0.19/0.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.55  thf('55', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.19/0.55      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.19/0.55  thf(t49_zfmisc_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.19/0.55  thf('56', plain,
% 0.19/0.55      (![X14 : $i, X15 : $i]:
% 0.19/0.55         ((k2_xboole_0 @ (k1_tarski @ X14) @ X15) != (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.19/0.55  thf('57', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.55  thf('58', plain,
% 0.19/0.55      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.19/0.55       ~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('simplify_reflect-', [status(thm)], ['54', '57'])).
% 0.19/0.55  thf('59', plain,
% 0.19/0.55      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.19/0.55       (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('split', [status(esa)], ['29'])).
% 0.19/0.55  thf('60', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.55      inference('sat_resolution*', [status(thm)], ['32', '58', '59'])).
% 0.19/0.55  thf('61', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.19/0.55      inference('simpl_trail', [status(thm)], ['30', '60'])).
% 0.19/0.55  thf('62', plain,
% 0.19/0.55      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.55      inference('sup-', [status(thm)], ['28', '61'])).
% 0.19/0.55  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('64', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.19/0.55      inference('demod', [status(thm)], ['62', '63'])).
% 0.19/0.55  thf('65', plain,
% 0.19/0.55      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.19/0.55         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('split', [status(esa)], ['31'])).
% 0.19/0.55  thf('66', plain, (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('sat_resolution*', [status(thm)], ['32', '58'])).
% 0.19/0.55  thf('67', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.19/0.55      inference('simpl_trail', [status(thm)], ['65', '66'])).
% 0.19/0.55  thf('68', plain, ($false),
% 0.19/0.55      inference('simplify_reflect-', [status(thm)], ['64', '67'])).
% 0.19/0.55  
% 0.19/0.55  % SZS output end Refutation
% 0.19/0.55  
% 0.19/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
