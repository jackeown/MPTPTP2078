%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KMZp8sA3iW

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:58 EST 2020

% Result     : Theorem 30.77s
% Output     : Refutation 30.77s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 599 expanded)
%              Number of leaves         :   38 ( 205 expanded)
%              Depth                    :   23
%              Number of atoms          : 1157 (4365 expanded)
%              Number of equality atoms :   55 ( 271 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X63: $i] :
      ( ( ( k3_relat_1 @ X63 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X63 ) @ ( k2_relat_1 @ X63 ) ) )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v1_relat_1 @ X64 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ X65 ) @ ( k1_relat_1 @ X64 ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ X65 @ X64 ) ) )
      | ~ ( v1_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t15_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k6_subset_1 @ X45 @ X46 )
      = ( k4_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k6_subset_1 @ X45 @ X46 )
      = ( k4_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v1_relat_1 @ X64 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X65 ) @ ( k1_relat_1 @ X64 ) ) @ ( k1_relat_1 @ ( k4_xboole_0 @ X65 @ X64 ) ) )
      | ~ ( v1_relat_1 @ X65 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ( ( k1_relat_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
      = ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('14',plain,(
    ! [X51: $i,X54: $i] :
      ( ( X54
        = ( k1_relat_1 @ X51 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X54 @ X51 ) @ ( sk_D @ X54 @ X51 ) ) @ X51 )
      | ( r2_hidden @ ( sk_C_1 @ X54 @ X51 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('16',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('17',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X32: $i,X34: $i] :
      ( ( r1_xboole_0 @ X32 @ X34 )
      | ( ( k4_xboole_0 @ X32 @ X34 )
       != X32 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('28',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','25'])).

thf('29',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('32',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('33',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['13','29','30','31','32','33','34'])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('44',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('45',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ X35 @ X36 )
      | ~ ( r1_tarski @ X37 @ X36 )
      | ( r1_tarski @ ( k2_xboole_0 @ X35 @ X37 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('49',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','51'])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('57',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X63: $i] :
      ( ( ( k3_relat_1 @ X63 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X63 ) @ ( k2_relat_1 @ X63 ) ) )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('59',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('60',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('61',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X12 @ ( k2_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t28_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('73',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( v1_relat_1 @ X66 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ X67 ) @ ( k2_relat_1 @ X66 ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ X67 @ X66 ) ) )
      | ~ ( v1_relat_1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t28_relat_1])).

thf('74',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k6_subset_1 @ X45 @ X46 )
      = ( k4_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('75',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k6_subset_1 @ X45 @ X46 )
      = ( k4_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('76',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( v1_relat_1 @ X66 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X67 ) @ ( k2_relat_1 @ X66 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X67 @ X66 ) ) )
      | ~ ( v1_relat_1 @ X67 ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) )
    | ( ( k2_relat_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
      = ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('80',plain,(
    ! [X58: $i,X61: $i] :
      ( ( X61
        = ( k2_relat_1 @ X58 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X61 @ X58 ) @ ( sk_C_2 @ X61 @ X58 ) ) @ X58 )
      | ( r2_hidden @ ( sk_C_2 @ X61 @ X58 ) @ X61 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('81',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','25'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','25'])).

thf('84',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('86',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('87',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('88',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['79','84','85','86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('97',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('99',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X63: $i] :
      ( ( ( k3_relat_1 @ X63 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X63 ) @ ( k2_relat_1 @ X63 ) ) )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('101',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('102',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X12 @ ( k2_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k3_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','105'])).

thf('107',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['99','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('111',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('114',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ X35 @ X36 )
      | ~ ( r1_tarski @ X37 @ X36 )
      | ( r1_tarski @ ( k2_xboole_0 @ X35 @ X37 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('123',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['111','120','123'])).

thf('125',plain,(
    $false ),
    inference(demod,[status(thm)],['0','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KMZp8sA3iW
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:09:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 30.77/31.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 30.77/31.01  % Solved by: fo/fo7.sh
% 30.77/31.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 30.77/31.01  % done 30458 iterations in 30.526s
% 30.77/31.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 30.77/31.01  % SZS output start Refutation
% 30.77/31.01  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 30.77/31.01  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 30.77/31.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 30.77/31.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 30.77/31.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 30.77/31.01  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 30.77/31.01  thf(sk_B_1_type, type, sk_B_1: $i).
% 30.77/31.01  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 30.77/31.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 30.77/31.01  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 30.77/31.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 30.77/31.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 30.77/31.01  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 30.77/31.01  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 30.77/31.01  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 30.77/31.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 30.77/31.01  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 30.77/31.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 30.77/31.01  thf(sk_A_type, type, sk_A: $i).
% 30.77/31.01  thf(t31_relat_1, conjecture,
% 30.77/31.01    (![A:$i]:
% 30.77/31.01     ( ( v1_relat_1 @ A ) =>
% 30.77/31.01       ( ![B:$i]:
% 30.77/31.01         ( ( v1_relat_1 @ B ) =>
% 30.77/31.01           ( ( r1_tarski @ A @ B ) =>
% 30.77/31.01             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 30.77/31.01  thf(zf_stmt_0, negated_conjecture,
% 30.77/31.01    (~( ![A:$i]:
% 30.77/31.01        ( ( v1_relat_1 @ A ) =>
% 30.77/31.01          ( ![B:$i]:
% 30.77/31.01            ( ( v1_relat_1 @ B ) =>
% 30.77/31.01              ( ( r1_tarski @ A @ B ) =>
% 30.77/31.01                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 30.77/31.01    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 30.77/31.01  thf('0', plain,
% 30.77/31.01      (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 30.77/31.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.77/31.01  thf(d6_relat_1, axiom,
% 30.77/31.01    (![A:$i]:
% 30.77/31.01     ( ( v1_relat_1 @ A ) =>
% 30.77/31.01       ( ( k3_relat_1 @ A ) =
% 30.77/31.01         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 30.77/31.01  thf('1', plain,
% 30.77/31.01      (![X63 : $i]:
% 30.77/31.01         (((k3_relat_1 @ X63)
% 30.77/31.01            = (k2_xboole_0 @ (k1_relat_1 @ X63) @ (k2_relat_1 @ X63)))
% 30.77/31.01          | ~ (v1_relat_1 @ X63))),
% 30.77/31.01      inference('cnf', [status(esa)], [d6_relat_1])).
% 30.77/31.01  thf(t7_xboole_1, axiom,
% 30.77/31.01    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 30.77/31.01  thf('2', plain,
% 30.77/31.01      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 30.77/31.01      inference('cnf', [status(esa)], [t7_xboole_1])).
% 30.77/31.01  thf('3', plain,
% 30.77/31.01      (![X0 : $i]:
% 30.77/31.01         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 30.77/31.01          | ~ (v1_relat_1 @ X0))),
% 30.77/31.01      inference('sup+', [status(thm)], ['1', '2'])).
% 30.77/31.01  thf('4', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 30.77/31.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.77/31.01  thf(l32_xboole_1, axiom,
% 30.77/31.01    (![A:$i,B:$i]:
% 30.77/31.01     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 30.77/31.01  thf('5', plain,
% 30.77/31.01      (![X9 : $i, X11 : $i]:
% 30.77/31.01         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 30.77/31.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 30.77/31.01  thf('6', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['4', '5'])).
% 30.77/31.01  thf(t15_relat_1, axiom,
% 30.77/31.01    (![A:$i]:
% 30.77/31.01     ( ( v1_relat_1 @ A ) =>
% 30.77/31.01       ( ![B:$i]:
% 30.77/31.01         ( ( v1_relat_1 @ B ) =>
% 30.77/31.01           ( r1_tarski @
% 30.77/31.01             ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ 
% 30.77/31.01             ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 30.77/31.01  thf('7', plain,
% 30.77/31.01      (![X64 : $i, X65 : $i]:
% 30.77/31.01         (~ (v1_relat_1 @ X64)
% 30.77/31.01          | (r1_tarski @ 
% 30.77/31.01             (k6_subset_1 @ (k1_relat_1 @ X65) @ (k1_relat_1 @ X64)) @ 
% 30.77/31.01             (k1_relat_1 @ (k6_subset_1 @ X65 @ X64)))
% 30.77/31.01          | ~ (v1_relat_1 @ X65))),
% 30.77/31.01      inference('cnf', [status(esa)], [t15_relat_1])).
% 30.77/31.01  thf(redefinition_k6_subset_1, axiom,
% 30.77/31.01    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 30.77/31.01  thf('8', plain,
% 30.77/31.01      (![X45 : $i, X46 : $i]:
% 30.77/31.01         ((k6_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))),
% 30.77/31.01      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 30.77/31.01  thf('9', plain,
% 30.77/31.01      (![X45 : $i, X46 : $i]:
% 30.77/31.01         ((k6_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))),
% 30.77/31.01      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 30.77/31.01  thf('10', plain,
% 30.77/31.01      (![X64 : $i, X65 : $i]:
% 30.77/31.01         (~ (v1_relat_1 @ X64)
% 30.77/31.01          | (r1_tarski @ 
% 30.77/31.01             (k4_xboole_0 @ (k1_relat_1 @ X65) @ (k1_relat_1 @ X64)) @ 
% 30.77/31.01             (k1_relat_1 @ (k4_xboole_0 @ X65 @ X64)))
% 30.77/31.01          | ~ (v1_relat_1 @ X65))),
% 30.77/31.01      inference('demod', [status(thm)], ['7', '8', '9'])).
% 30.77/31.01  thf(d10_xboole_0, axiom,
% 30.77/31.01    (![A:$i,B:$i]:
% 30.77/31.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 30.77/31.01  thf('11', plain,
% 30.77/31.01      (![X6 : $i, X8 : $i]:
% 30.77/31.01         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 30.77/31.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.77/31.01  thf('12', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]:
% 30.77/31.01         (~ (v1_relat_1 @ X1)
% 30.77/31.01          | ~ (v1_relat_1 @ X0)
% 30.77/31.01          | ~ (r1_tarski @ (k1_relat_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 30.77/31.01               (k4_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)))
% 30.77/31.01          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ X0))
% 30.77/31.01              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0))))),
% 30.77/31.01      inference('sup-', [status(thm)], ['10', '11'])).
% 30.77/31.01  thf('13', plain,
% 30.77/31.01      ((~ (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ 
% 30.77/31.01           (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))
% 30.77/31.01        | ((k1_relat_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 30.77/31.01            = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))
% 30.77/31.01        | ~ (v1_relat_1 @ sk_B_1)
% 30.77/31.01        | ~ (v1_relat_1 @ sk_A))),
% 30.77/31.01      inference('sup-', [status(thm)], ['6', '12'])).
% 30.77/31.01  thf(d4_relat_1, axiom,
% 30.77/31.01    (![A:$i,B:$i]:
% 30.77/31.01     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 30.77/31.01       ( ![C:$i]:
% 30.77/31.01         ( ( r2_hidden @ C @ B ) <=>
% 30.77/31.01           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 30.77/31.01  thf('14', plain,
% 30.77/31.01      (![X51 : $i, X54 : $i]:
% 30.77/31.01         (((X54) = (k1_relat_1 @ X51))
% 30.77/31.01          | (r2_hidden @ 
% 30.77/31.01             (k4_tarski @ (sk_C_1 @ X54 @ X51) @ (sk_D @ X54 @ X51)) @ X51)
% 30.77/31.01          | (r2_hidden @ (sk_C_1 @ X54 @ X51) @ X54))),
% 30.77/31.01      inference('cnf', [status(esa)], [d4_relat_1])).
% 30.77/31.01  thf(t48_xboole_1, axiom,
% 30.77/31.01    (![A:$i,B:$i]:
% 30.77/31.01     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 30.77/31.01  thf('15', plain,
% 30.77/31.01      (![X28 : $i, X29 : $i]:
% 30.77/31.01         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 30.77/31.01           = (k3_xboole_0 @ X28 @ X29))),
% 30.77/31.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 30.77/31.01  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 30.77/31.01  thf('16', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 30.77/31.01      inference('cnf', [status(esa)], [t2_xboole_1])).
% 30.77/31.01  thf('17', plain,
% 30.77/31.01      (![X9 : $i, X11 : $i]:
% 30.77/31.01         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 30.77/31.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 30.77/31.01  thf('18', plain,
% 30.77/31.01      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['16', '17'])).
% 30.77/31.01  thf('19', plain,
% 30.77/31.01      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 30.77/31.01      inference('sup+', [status(thm)], ['15', '18'])).
% 30.77/31.01  thf(t4_xboole_0, axiom,
% 30.77/31.01    (![A:$i,B:$i]:
% 30.77/31.01     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 30.77/31.01            ( r1_xboole_0 @ A @ B ) ) ) & 
% 30.77/31.01       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 30.77/31.01            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 30.77/31.01  thf('20', plain,
% 30.77/31.01      (![X1 : $i, X3 : $i, X4 : $i]:
% 30.77/31.01         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 30.77/31.01          | ~ (r1_xboole_0 @ X1 @ X4))),
% 30.77/31.01      inference('cnf', [status(esa)], [t4_xboole_0])).
% 30.77/31.01  thf('21', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]:
% 30.77/31.01         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['19', '20'])).
% 30.77/31.01  thf('22', plain,
% 30.77/31.01      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['16', '17'])).
% 30.77/31.01  thf(t83_xboole_1, axiom,
% 30.77/31.01    (![A:$i,B:$i]:
% 30.77/31.01     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 30.77/31.01  thf('23', plain,
% 30.77/31.01      (![X32 : $i, X34 : $i]:
% 30.77/31.01         ((r1_xboole_0 @ X32 @ X34) | ((k4_xboole_0 @ X32 @ X34) != (X32)))),
% 30.77/31.01      inference('cnf', [status(esa)], [t83_xboole_1])).
% 30.77/31.01  thf('24', plain,
% 30.77/31.01      (![X0 : $i]:
% 30.77/31.01         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['22', '23'])).
% 30.77/31.01  thf('25', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 30.77/31.01      inference('simplify', [status(thm)], ['24'])).
% 30.77/31.01  thf('26', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 30.77/31.01      inference('demod', [status(thm)], ['21', '25'])).
% 30.77/31.01  thf('27', plain,
% 30.77/31.01      (![X0 : $i]:
% 30.77/31.01         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 30.77/31.01          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 30.77/31.01      inference('sup-', [status(thm)], ['14', '26'])).
% 30.77/31.01  thf('28', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 30.77/31.01      inference('demod', [status(thm)], ['21', '25'])).
% 30.77/31.01  thf('29', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['27', '28'])).
% 30.77/31.01  thf('30', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 30.77/31.01      inference('cnf', [status(esa)], [t2_xboole_1])).
% 30.77/31.01  thf('31', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['4', '5'])).
% 30.77/31.01  thf('32', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['27', '28'])).
% 30.77/31.01  thf('33', plain, ((v1_relat_1 @ sk_B_1)),
% 30.77/31.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.77/31.01  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 30.77/31.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.77/31.01  thf('35', plain,
% 30.77/31.01      (((k1_xboole_0)
% 30.77/31.01         = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))),
% 30.77/31.01      inference('demod', [status(thm)],
% 30.77/31.01                ['13', '29', '30', '31', '32', '33', '34'])).
% 30.77/31.01  thf('36', plain,
% 30.77/31.01      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 30.77/31.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.77/31.01  thf('37', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 30.77/31.01      inference('simplify', [status(thm)], ['36'])).
% 30.77/31.01  thf(t44_xboole_1, axiom,
% 30.77/31.01    (![A:$i,B:$i,C:$i]:
% 30.77/31.01     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 30.77/31.01       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 30.77/31.01  thf('38', plain,
% 30.77/31.01      (![X25 : $i, X26 : $i, X27 : $i]:
% 30.77/31.01         ((r1_tarski @ X25 @ (k2_xboole_0 @ X26 @ X27))
% 30.77/31.01          | ~ (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27))),
% 30.77/31.01      inference('cnf', [status(esa)], [t44_xboole_1])).
% 30.77/31.01  thf('39', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]:
% 30.77/31.01         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 30.77/31.01      inference('sup-', [status(thm)], ['37', '38'])).
% 30.77/31.01  thf(t1_xboole_1, axiom,
% 30.77/31.01    (![A:$i,B:$i,C:$i]:
% 30.77/31.01     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 30.77/31.01       ( r1_tarski @ A @ C ) ))).
% 30.77/31.01  thf('40', plain,
% 30.77/31.01      (![X15 : $i, X16 : $i, X17 : $i]:
% 30.77/31.01         (~ (r1_tarski @ X15 @ X16)
% 30.77/31.01          | ~ (r1_tarski @ X16 @ X17)
% 30.77/31.01          | (r1_tarski @ X15 @ X17))),
% 30.77/31.01      inference('cnf', [status(esa)], [t1_xboole_1])).
% 30.77/31.01  thf('41', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.77/31.01         ((r1_tarski @ X1 @ X2)
% 30.77/31.01          | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2))),
% 30.77/31.01      inference('sup-', [status(thm)], ['39', '40'])).
% 30.77/31.01  thf('42', plain,
% 30.77/31.01      (![X0 : $i]:
% 30.77/31.01         (~ (r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_B_1) @ k1_xboole_0) @ 
% 30.77/31.01             X0)
% 30.77/31.01          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['35', '41'])).
% 30.77/31.01  thf('43', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 30.77/31.01      inference('cnf', [status(esa)], [t2_xboole_1])).
% 30.77/31.01  thf('44', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 30.77/31.01      inference('simplify', [status(thm)], ['36'])).
% 30.77/31.01  thf(t8_xboole_1, axiom,
% 30.77/31.01    (![A:$i,B:$i,C:$i]:
% 30.77/31.01     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 30.77/31.01       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 30.77/31.01  thf('45', plain,
% 30.77/31.01      (![X35 : $i, X36 : $i, X37 : $i]:
% 30.77/31.01         (~ (r1_tarski @ X35 @ X36)
% 30.77/31.01          | ~ (r1_tarski @ X37 @ X36)
% 30.77/31.01          | (r1_tarski @ (k2_xboole_0 @ X35 @ X37) @ X36))),
% 30.77/31.01      inference('cnf', [status(esa)], [t8_xboole_1])).
% 30.77/31.01  thf('46', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]:
% 30.77/31.01         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['44', '45'])).
% 30.77/31.01  thf('47', plain,
% 30.77/31.01      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 30.77/31.01      inference('sup-', [status(thm)], ['43', '46'])).
% 30.77/31.01  thf('48', plain,
% 30.77/31.01      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 30.77/31.01      inference('cnf', [status(esa)], [t7_xboole_1])).
% 30.77/31.01  thf('49', plain,
% 30.77/31.01      (![X6 : $i, X8 : $i]:
% 30.77/31.01         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 30.77/31.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.77/31.01  thf('50', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]:
% 30.77/31.01         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 30.77/31.01          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 30.77/31.01      inference('sup-', [status(thm)], ['48', '49'])).
% 30.77/31.01  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['47', '50'])).
% 30.77/31.01  thf('52', plain,
% 30.77/31.01      (![X0 : $i]:
% 30.77/31.01         (~ (r1_tarski @ (k1_relat_1 @ sk_B_1) @ X0)
% 30.77/31.01          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 30.77/31.01      inference('demod', [status(thm)], ['42', '51'])).
% 30.77/31.01  thf('53', plain,
% 30.77/31.01      ((~ (v1_relat_1 @ sk_B_1)
% 30.77/31.01        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1)))),
% 30.77/31.01      inference('sup-', [status(thm)], ['3', '52'])).
% 30.77/31.01  thf('54', plain, ((v1_relat_1 @ sk_B_1)),
% 30.77/31.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.77/31.01  thf('55', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 30.77/31.01      inference('demod', [status(thm)], ['53', '54'])).
% 30.77/31.01  thf('56', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]:
% 30.77/31.01         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['44', '45'])).
% 30.77/31.01  thf('57', plain,
% 30.77/31.01      ((r1_tarski @ 
% 30.77/31.01        (k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)) @ 
% 30.77/31.01        (k3_relat_1 @ sk_B_1))),
% 30.77/31.01      inference('sup-', [status(thm)], ['55', '56'])).
% 30.77/31.01  thf('58', plain,
% 30.77/31.01      (![X63 : $i]:
% 30.77/31.01         (((k3_relat_1 @ X63)
% 30.77/31.01            = (k2_xboole_0 @ (k1_relat_1 @ X63) @ (k2_relat_1 @ X63)))
% 30.77/31.01          | ~ (v1_relat_1 @ X63))),
% 30.77/31.01      inference('cnf', [status(esa)], [d6_relat_1])).
% 30.77/31.01  thf('59', plain,
% 30.77/31.01      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 30.77/31.01      inference('cnf', [status(esa)], [t7_xboole_1])).
% 30.77/31.01  thf('60', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 30.77/31.01      inference('simplify', [status(thm)], ['36'])).
% 30.77/31.01  thf(t10_xboole_1, axiom,
% 30.77/31.01    (![A:$i,B:$i,C:$i]:
% 30.77/31.01     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 30.77/31.01  thf('61', plain,
% 30.77/31.01      (![X12 : $i, X13 : $i, X14 : $i]:
% 30.77/31.01         (~ (r1_tarski @ X12 @ X13)
% 30.77/31.01          | (r1_tarski @ X12 @ (k2_xboole_0 @ X14 @ X13)))),
% 30.77/31.01      inference('cnf', [status(esa)], [t10_xboole_1])).
% 30.77/31.01  thf('62', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['60', '61'])).
% 30.77/31.01  thf('63', plain,
% 30.77/31.01      (![X15 : $i, X16 : $i, X17 : $i]:
% 30.77/31.01         (~ (r1_tarski @ X15 @ X16)
% 30.77/31.01          | ~ (r1_tarski @ X16 @ X17)
% 30.77/31.01          | (r1_tarski @ X15 @ X17))),
% 30.77/31.01      inference('cnf', [status(esa)], [t1_xboole_1])).
% 30.77/31.01  thf('64', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.77/31.01         ((r1_tarski @ X0 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 30.77/31.01      inference('sup-', [status(thm)], ['62', '63'])).
% 30.77/31.01  thf('65', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.77/31.01         (r1_tarski @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['59', '64'])).
% 30.77/31.01  thf('66', plain,
% 30.77/31.01      (![X15 : $i, X16 : $i, X17 : $i]:
% 30.77/31.01         (~ (r1_tarski @ X15 @ X16)
% 30.77/31.01          | ~ (r1_tarski @ X16 @ X17)
% 30.77/31.01          | (r1_tarski @ X15 @ X17))),
% 30.77/31.01      inference('cnf', [status(esa)], [t1_xboole_1])).
% 30.77/31.01  thf('67', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 30.77/31.01         ((r1_tarski @ X1 @ X3)
% 30.77/31.01          | ~ (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ X3))),
% 30.77/31.01      inference('sup-', [status(thm)], ['65', '66'])).
% 30.77/31.01  thf('68', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.77/31.01         (~ (r1_tarski @ (k2_xboole_0 @ (k3_relat_1 @ X0) @ X2) @ X1)
% 30.77/31.01          | ~ (v1_relat_1 @ X0)
% 30.77/31.01          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 30.77/31.01      inference('sup-', [status(thm)], ['58', '67'])).
% 30.77/31.01  thf('69', plain,
% 30.77/31.01      (((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))
% 30.77/31.01        | ~ (v1_relat_1 @ sk_B_1))),
% 30.77/31.01      inference('sup-', [status(thm)], ['57', '68'])).
% 30.77/31.01  thf('70', plain, ((v1_relat_1 @ sk_B_1)),
% 30.77/31.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.77/31.01  thf('71', plain,
% 30.77/31.01      ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))),
% 30.77/31.01      inference('demod', [status(thm)], ['69', '70'])).
% 30.77/31.01  thf('72', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['4', '5'])).
% 30.77/31.01  thf(t28_relat_1, axiom,
% 30.77/31.01    (![A:$i]:
% 30.77/31.01     ( ( v1_relat_1 @ A ) =>
% 30.77/31.01       ( ![B:$i]:
% 30.77/31.01         ( ( v1_relat_1 @ B ) =>
% 30.77/31.01           ( r1_tarski @
% 30.77/31.01             ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 30.77/31.01             ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 30.77/31.01  thf('73', plain,
% 30.77/31.01      (![X66 : $i, X67 : $i]:
% 30.77/31.01         (~ (v1_relat_1 @ X66)
% 30.77/31.01          | (r1_tarski @ 
% 30.77/31.01             (k6_subset_1 @ (k2_relat_1 @ X67) @ (k2_relat_1 @ X66)) @ 
% 30.77/31.01             (k2_relat_1 @ (k6_subset_1 @ X67 @ X66)))
% 30.77/31.01          | ~ (v1_relat_1 @ X67))),
% 30.77/31.01      inference('cnf', [status(esa)], [t28_relat_1])).
% 30.77/31.01  thf('74', plain,
% 30.77/31.01      (![X45 : $i, X46 : $i]:
% 30.77/31.01         ((k6_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))),
% 30.77/31.01      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 30.77/31.01  thf('75', plain,
% 30.77/31.01      (![X45 : $i, X46 : $i]:
% 30.77/31.01         ((k6_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))),
% 30.77/31.01      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 30.77/31.01  thf('76', plain,
% 30.77/31.01      (![X66 : $i, X67 : $i]:
% 30.77/31.01         (~ (v1_relat_1 @ X66)
% 30.77/31.01          | (r1_tarski @ 
% 30.77/31.01             (k4_xboole_0 @ (k2_relat_1 @ X67) @ (k2_relat_1 @ X66)) @ 
% 30.77/31.01             (k2_relat_1 @ (k4_xboole_0 @ X67 @ X66)))
% 30.77/31.01          | ~ (v1_relat_1 @ X67))),
% 30.77/31.01      inference('demod', [status(thm)], ['73', '74', '75'])).
% 30.77/31.01  thf('77', plain,
% 30.77/31.01      (![X6 : $i, X8 : $i]:
% 30.77/31.01         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 30.77/31.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.77/31.01  thf('78', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]:
% 30.77/31.01         (~ (v1_relat_1 @ X1)
% 30.77/31.01          | ~ (v1_relat_1 @ X0)
% 30.77/31.01          | ~ (r1_tarski @ (k2_relat_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 30.77/31.01               (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 30.77/31.01          | ((k2_relat_1 @ (k4_xboole_0 @ X1 @ X0))
% 30.77/31.01              = (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))))),
% 30.77/31.01      inference('sup-', [status(thm)], ['76', '77'])).
% 30.77/31.01  thf('79', plain,
% 30.77/31.01      ((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ 
% 30.77/31.01           (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))
% 30.77/31.01        | ((k2_relat_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 30.77/31.01            = (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))
% 30.77/31.01        | ~ (v1_relat_1 @ sk_B_1)
% 30.77/31.01        | ~ (v1_relat_1 @ sk_A))),
% 30.77/31.01      inference('sup-', [status(thm)], ['72', '78'])).
% 30.77/31.01  thf(d5_relat_1, axiom,
% 30.77/31.01    (![A:$i,B:$i]:
% 30.77/31.01     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 30.77/31.01       ( ![C:$i]:
% 30.77/31.01         ( ( r2_hidden @ C @ B ) <=>
% 30.77/31.01           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 30.77/31.01  thf('80', plain,
% 30.77/31.01      (![X58 : $i, X61 : $i]:
% 30.77/31.01         (((X61) = (k2_relat_1 @ X58))
% 30.77/31.01          | (r2_hidden @ 
% 30.77/31.01             (k4_tarski @ (sk_D_2 @ X61 @ X58) @ (sk_C_2 @ X61 @ X58)) @ X58)
% 30.77/31.01          | (r2_hidden @ (sk_C_2 @ X61 @ X58) @ X61))),
% 30.77/31.01      inference('cnf', [status(esa)], [d5_relat_1])).
% 30.77/31.01  thf('81', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 30.77/31.01      inference('demod', [status(thm)], ['21', '25'])).
% 30.77/31.01  thf('82', plain,
% 30.77/31.01      (![X0 : $i]:
% 30.77/31.01         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 30.77/31.01          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 30.77/31.01      inference('sup-', [status(thm)], ['80', '81'])).
% 30.77/31.01  thf('83', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 30.77/31.01      inference('demod', [status(thm)], ['21', '25'])).
% 30.77/31.01  thf('84', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['82', '83'])).
% 30.77/31.01  thf('85', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 30.77/31.01      inference('cnf', [status(esa)], [t2_xboole_1])).
% 30.77/31.01  thf('86', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['4', '5'])).
% 30.77/31.01  thf('87', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['82', '83'])).
% 30.77/31.01  thf('88', plain, ((v1_relat_1 @ sk_B_1)),
% 30.77/31.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.77/31.01  thf('89', plain, ((v1_relat_1 @ sk_A)),
% 30.77/31.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.77/31.01  thf('90', plain,
% 30.77/31.01      (((k1_xboole_0)
% 30.77/31.01         = (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))),
% 30.77/31.01      inference('demod', [status(thm)],
% 30.77/31.01                ['79', '84', '85', '86', '87', '88', '89'])).
% 30.77/31.01  thf('91', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.77/31.01         ((r1_tarski @ X1 @ X2)
% 30.77/31.01          | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2))),
% 30.77/31.01      inference('sup-', [status(thm)], ['39', '40'])).
% 30.77/31.01  thf('92', plain,
% 30.77/31.01      (![X0 : $i]:
% 30.77/31.01         (~ (r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_B_1) @ k1_xboole_0) @ 
% 30.77/31.01             X0)
% 30.77/31.01          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['90', '91'])).
% 30.77/31.01  thf('93', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['47', '50'])).
% 30.77/31.01  thf('94', plain,
% 30.77/31.01      (![X0 : $i]:
% 30.77/31.01         (~ (r1_tarski @ (k2_relat_1 @ sk_B_1) @ X0)
% 30.77/31.01          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0))),
% 30.77/31.01      inference('demod', [status(thm)], ['92', '93'])).
% 30.77/31.01  thf('95', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 30.77/31.01      inference('sup-', [status(thm)], ['71', '94'])).
% 30.77/31.01  thf('96', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]:
% 30.77/31.01         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['44', '45'])).
% 30.77/31.01  thf('97', plain,
% 30.77/31.01      ((r1_tarski @ 
% 30.77/31.01        (k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_A)) @ 
% 30.77/31.01        (k3_relat_1 @ sk_B_1))),
% 30.77/31.01      inference('sup-', [status(thm)], ['95', '96'])).
% 30.77/31.01  thf('98', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]:
% 30.77/31.01         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 30.77/31.01          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 30.77/31.01      inference('sup-', [status(thm)], ['48', '49'])).
% 30.77/31.01  thf('99', plain,
% 30.77/31.01      (((k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_A))
% 30.77/31.01         = (k3_relat_1 @ sk_B_1))),
% 30.77/31.01      inference('sup-', [status(thm)], ['97', '98'])).
% 30.77/31.01  thf('100', plain,
% 30.77/31.01      (![X63 : $i]:
% 30.77/31.01         (((k3_relat_1 @ X63)
% 30.77/31.01            = (k2_xboole_0 @ (k1_relat_1 @ X63) @ (k2_relat_1 @ X63)))
% 30.77/31.01          | ~ (v1_relat_1 @ X63))),
% 30.77/31.01      inference('cnf', [status(esa)], [d6_relat_1])).
% 30.77/31.01  thf('101', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 30.77/31.01      inference('simplify', [status(thm)], ['36'])).
% 30.77/31.01  thf(t43_xboole_1, axiom,
% 30.77/31.01    (![A:$i,B:$i,C:$i]:
% 30.77/31.01     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 30.77/31.01       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 30.77/31.01  thf('102', plain,
% 30.77/31.01      (![X22 : $i, X23 : $i, X24 : $i]:
% 30.77/31.01         ((r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 30.77/31.01          | ~ (r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 30.77/31.01      inference('cnf', [status(esa)], [t43_xboole_1])).
% 30.77/31.01  thf('103', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]:
% 30.77/31.01         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 30.77/31.01      inference('sup-', [status(thm)], ['101', '102'])).
% 30.77/31.01  thf('104', plain,
% 30.77/31.01      (![X12 : $i, X13 : $i, X14 : $i]:
% 30.77/31.01         (~ (r1_tarski @ X12 @ X13)
% 30.77/31.01          | (r1_tarski @ X12 @ (k2_xboole_0 @ X14 @ X13)))),
% 30.77/31.01      inference('cnf', [status(esa)], [t10_xboole_1])).
% 30.77/31.01  thf('105', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.77/31.01         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ 
% 30.77/31.01          (k2_xboole_0 @ X2 @ X0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['103', '104'])).
% 30.77/31.01  thf('106', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]:
% 30.77/31.01         ((r1_tarski @ (k4_xboole_0 @ (k3_relat_1 @ X0) @ (k1_relat_1 @ X0)) @ 
% 30.77/31.01           (k2_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 30.77/31.01          | ~ (v1_relat_1 @ X0))),
% 30.77/31.01      inference('sup+', [status(thm)], ['100', '105'])).
% 30.77/31.01  thf('107', plain,
% 30.77/31.01      (((r1_tarski @ 
% 30.77/31.01         (k4_xboole_0 @ (k3_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 30.77/31.01         (k3_relat_1 @ sk_B_1))
% 30.77/31.01        | ~ (v1_relat_1 @ sk_A))),
% 30.77/31.01      inference('sup+', [status(thm)], ['99', '106'])).
% 30.77/31.01  thf('108', plain, ((v1_relat_1 @ sk_A)),
% 30.77/31.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.77/31.01  thf('109', plain,
% 30.77/31.01      ((r1_tarski @ 
% 30.77/31.01        (k4_xboole_0 @ (k3_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 30.77/31.01        (k3_relat_1 @ sk_B_1))),
% 30.77/31.01      inference('demod', [status(thm)], ['107', '108'])).
% 30.77/31.01  thf('110', plain,
% 30.77/31.01      (![X25 : $i, X26 : $i, X27 : $i]:
% 30.77/31.01         ((r1_tarski @ X25 @ (k2_xboole_0 @ X26 @ X27))
% 30.77/31.01          | ~ (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27))),
% 30.77/31.01      inference('cnf', [status(esa)], [t44_xboole_1])).
% 30.77/31.01  thf('111', plain,
% 30.77/31.01      ((r1_tarski @ (k3_relat_1 @ sk_A) @ 
% 30.77/31.01        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1)))),
% 30.77/31.01      inference('sup-', [status(thm)], ['109', '110'])).
% 30.77/31.01  thf('112', plain,
% 30.77/31.01      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 30.77/31.01      inference('cnf', [status(esa)], [t7_xboole_1])).
% 30.77/31.01  thf('113', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['60', '61'])).
% 30.77/31.01  thf('114', plain,
% 30.77/31.01      (![X35 : $i, X36 : $i, X37 : $i]:
% 30.77/31.01         (~ (r1_tarski @ X35 @ X36)
% 30.77/31.01          | ~ (r1_tarski @ X37 @ X36)
% 30.77/31.01          | (r1_tarski @ (k2_xboole_0 @ X35 @ X37) @ X36))),
% 30.77/31.01      inference('cnf', [status(esa)], [t8_xboole_1])).
% 30.77/31.01  thf('115', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.77/31.01         ((r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 30.77/31.01          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 30.77/31.01      inference('sup-', [status(thm)], ['113', '114'])).
% 30.77/31.01  thf('116', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]:
% 30.77/31.01         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['112', '115'])).
% 30.77/31.01  thf('117', plain,
% 30.77/31.01      (![X6 : $i, X8 : $i]:
% 30.77/31.01         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 30.77/31.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.77/31.01  thf('118', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]:
% 30.77/31.01         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 30.77/31.01          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1)))),
% 30.77/31.01      inference('sup-', [status(thm)], ['116', '117'])).
% 30.77/31.01  thf('119', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]:
% 30.77/31.01         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 30.77/31.01      inference('sup-', [status(thm)], ['112', '115'])).
% 30.77/31.01  thf('120', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 30.77/31.01      inference('demod', [status(thm)], ['118', '119'])).
% 30.77/31.01  thf('121', plain,
% 30.77/31.01      ((r1_tarski @ 
% 30.77/31.01        (k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)) @ 
% 30.77/31.01        (k3_relat_1 @ sk_B_1))),
% 30.77/31.01      inference('sup-', [status(thm)], ['55', '56'])).
% 30.77/31.01  thf('122', plain,
% 30.77/31.01      (![X0 : $i, X1 : $i]:
% 30.77/31.01         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 30.77/31.01          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 30.77/31.01      inference('sup-', [status(thm)], ['48', '49'])).
% 30.77/31.01  thf('123', plain,
% 30.77/31.01      (((k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))
% 30.77/31.01         = (k3_relat_1 @ sk_B_1))),
% 30.77/31.01      inference('sup-', [status(thm)], ['121', '122'])).
% 30.77/31.01  thf('124', plain,
% 30.77/31.01      ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 30.77/31.01      inference('demod', [status(thm)], ['111', '120', '123'])).
% 30.77/31.01  thf('125', plain, ($false), inference('demod', [status(thm)], ['0', '124'])).
% 30.77/31.01  
% 30.77/31.01  % SZS output end Refutation
% 30.77/31.01  
% 30.77/31.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
