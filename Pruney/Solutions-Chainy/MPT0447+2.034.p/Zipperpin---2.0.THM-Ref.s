%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aYrME0ufkK

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:57 EST 2020

% Result     : Theorem 27.80s
% Output     : Refutation 27.80s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 861 expanded)
%              Number of leaves         :   40 ( 291 expanded)
%              Depth                    :   23
%              Number of atoms          : 1453 (6457 expanded)
%              Number of equality atoms :   75 ( 435 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X56: $i] :
      ( ( ( k3_relat_1 @ X56 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) ) ),
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
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
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
    ! [X57: $i,X58: $i] :
      ( ~ ( v1_relat_1 @ X57 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ X58 ) @ ( k1_relat_1 @ X57 ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ X58 @ X57 ) ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t15_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( v1_relat_1 @ X57 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X58 ) @ ( k1_relat_1 @ X57 ) ) @ ( k1_relat_1 @ ( k4_xboole_0 @ X58 @ X57 ) ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
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
    ! [X44: $i,X47: $i] :
      ( ( X47
        = ( k1_relat_1 @ X44 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X47 @ X44 ) @ ( sk_D @ X47 @ X44 ) ) @ X44 )
      | ( r2_hidden @ ( sk_C_1 @ X47 @ X44 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','21'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('23',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('25',plain,(
    ! [X30: $i] :
      ( r1_xboole_0 @ X30 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('26',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('28',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('29',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X19: $i] :
      ( r1_tarski @ k1_xboole_0 @ X19 ) ),
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
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X19: $i] :
      ( r1_tarski @ k1_xboole_0 @ X19 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('43',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('44',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X33 @ X34 )
      | ~ ( r1_tarski @ X35 @ X34 )
      | ( r1_tarski @ ( k2_xboole_0 @ X33 @ X35 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('48',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['41','50'])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('56',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X56: $i] :
      ( ( ( k3_relat_1 @ X56 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('61',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k2_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ X3 )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t28_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('72',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( v1_relat_1 @ X59 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ X60 ) @ ( k2_relat_1 @ X59 ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ X60 @ X59 ) ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t28_relat_1])).

thf('73',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('74',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('75',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( v1_relat_1 @ X59 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X60 ) @ ( k2_relat_1 @ X59 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X60 @ X59 ) ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) )
    | ( ( k2_relat_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
      = ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','77'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('79',plain,(
    ! [X51: $i,X54: $i] :
      ( ( X54
        = ( k2_relat_1 @ X51 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X54 @ X51 ) @ ( sk_C_2 @ X54 @ X51 ) ) @ X51 )
      | ( r2_hidden @ ( sk_C_2 @ X54 @ X51 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('80',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('83',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X19: $i] :
      ( r1_tarski @ k1_xboole_0 @ X19 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('85',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('86',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('87',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['78','83','84','85','86','87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['70','93'])).

thf('95',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('96',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X33 @ X34 )
      | ~ ( r1_tarski @ X35 @ X34 )
      | ( r1_tarski @ ( k2_xboole_0 @ X33 @ X35 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B_1 ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['13','29','30','31','32','33','34'])).

thf('100',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('101',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('103',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('105',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('107',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('109',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['105','110'])).

thf('112',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','113'])).

thf('115',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['103','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('119',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('121',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('123',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('126',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['123','134'])).

thf('136',plain,(
    ! [X56: $i] :
      ( ( ( k3_relat_1 @ X56 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('137',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) @ ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['136','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) @ ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['135','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('149',plain,
    ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) )
    | ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
      = ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('151',plain,(
    ! [X56: $i] :
      ( ( ( k3_relat_1 @ X56 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X33 @ X34 )
      | ~ ( r1_tarski @ X35 @ X34 )
      | ( r1_tarski @ ( k2_xboole_0 @ X33 @ X35 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['150','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('158',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['149','159'])).

thf('161',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['98','160'])).

thf('162',plain,(
    $false ),
    inference(demod,[status(thm)],['0','161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aYrME0ufkK
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 27.80/28.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 27.80/28.04  % Solved by: fo/fo7.sh
% 27.80/28.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 27.80/28.04  % done 33433 iterations in 27.583s
% 27.80/28.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 27.80/28.04  % SZS output start Refutation
% 27.80/28.04  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 27.80/28.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 27.80/28.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 27.80/28.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 27.80/28.04  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 27.80/28.04  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 27.80/28.04  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 27.80/28.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 27.80/28.04  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 27.80/28.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 27.80/28.04  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 27.80/28.04  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 27.80/28.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 27.80/28.04  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 27.80/28.04  thf(sk_B_1_type, type, sk_B_1: $i).
% 27.80/28.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 27.80/28.04  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 27.80/28.04  thf(sk_A_type, type, sk_A: $i).
% 27.80/28.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 27.80/28.04  thf(t31_relat_1, conjecture,
% 27.80/28.04    (![A:$i]:
% 27.80/28.04     ( ( v1_relat_1 @ A ) =>
% 27.80/28.04       ( ![B:$i]:
% 27.80/28.04         ( ( v1_relat_1 @ B ) =>
% 27.80/28.04           ( ( r1_tarski @ A @ B ) =>
% 27.80/28.04             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 27.80/28.04  thf(zf_stmt_0, negated_conjecture,
% 27.80/28.04    (~( ![A:$i]:
% 27.80/28.04        ( ( v1_relat_1 @ A ) =>
% 27.80/28.04          ( ![B:$i]:
% 27.80/28.04            ( ( v1_relat_1 @ B ) =>
% 27.80/28.04              ( ( r1_tarski @ A @ B ) =>
% 27.80/28.04                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 27.80/28.04    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 27.80/28.04  thf('0', plain,
% 27.80/28.04      (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 27.80/28.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.80/28.04  thf(d6_relat_1, axiom,
% 27.80/28.04    (![A:$i]:
% 27.80/28.04     ( ( v1_relat_1 @ A ) =>
% 27.80/28.04       ( ( k3_relat_1 @ A ) =
% 27.80/28.04         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 27.80/28.04  thf('1', plain,
% 27.80/28.04      (![X56 : $i]:
% 27.80/28.04         (((k3_relat_1 @ X56)
% 27.80/28.04            = (k2_xboole_0 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56)))
% 27.80/28.04          | ~ (v1_relat_1 @ X56))),
% 27.80/28.04      inference('cnf', [status(esa)], [d6_relat_1])).
% 27.80/28.04  thf(t7_xboole_1, axiom,
% 27.80/28.04    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 27.80/28.04  thf('2', plain,
% 27.80/28.04      (![X31 : $i, X32 : $i]: (r1_tarski @ X31 @ (k2_xboole_0 @ X31 @ X32))),
% 27.80/28.04      inference('cnf', [status(esa)], [t7_xboole_1])).
% 27.80/28.04  thf('3', plain,
% 27.80/28.04      (![X0 : $i]:
% 27.80/28.04         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 27.80/28.04          | ~ (v1_relat_1 @ X0))),
% 27.80/28.04      inference('sup+', [status(thm)], ['1', '2'])).
% 27.80/28.04  thf('4', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 27.80/28.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.80/28.04  thf(l32_xboole_1, axiom,
% 27.80/28.04    (![A:$i,B:$i]:
% 27.80/28.04     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 27.80/28.04  thf('5', plain,
% 27.80/28.04      (![X10 : $i, X12 : $i]:
% 27.80/28.04         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 27.80/28.04          | ~ (r1_tarski @ X10 @ X12))),
% 27.80/28.04      inference('cnf', [status(esa)], [l32_xboole_1])).
% 27.80/28.04  thf('6', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['4', '5'])).
% 27.80/28.04  thf(t15_relat_1, axiom,
% 27.80/28.04    (![A:$i]:
% 27.80/28.04     ( ( v1_relat_1 @ A ) =>
% 27.80/28.04       ( ![B:$i]:
% 27.80/28.04         ( ( v1_relat_1 @ B ) =>
% 27.80/28.04           ( r1_tarski @
% 27.80/28.04             ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ 
% 27.80/28.04             ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 27.80/28.04  thf('7', plain,
% 27.80/28.04      (![X57 : $i, X58 : $i]:
% 27.80/28.04         (~ (v1_relat_1 @ X57)
% 27.80/28.04          | (r1_tarski @ 
% 27.80/28.04             (k6_subset_1 @ (k1_relat_1 @ X58) @ (k1_relat_1 @ X57)) @ 
% 27.80/28.04             (k1_relat_1 @ (k6_subset_1 @ X58 @ X57)))
% 27.80/28.04          | ~ (v1_relat_1 @ X58))),
% 27.80/28.04      inference('cnf', [status(esa)], [t15_relat_1])).
% 27.80/28.04  thf(redefinition_k6_subset_1, axiom,
% 27.80/28.04    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 27.80/28.04  thf('8', plain,
% 27.80/28.04      (![X38 : $i, X39 : $i]:
% 27.80/28.04         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 27.80/28.04      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 27.80/28.04  thf('9', plain,
% 27.80/28.04      (![X38 : $i, X39 : $i]:
% 27.80/28.04         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 27.80/28.04      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 27.80/28.04  thf('10', plain,
% 27.80/28.04      (![X57 : $i, X58 : $i]:
% 27.80/28.04         (~ (v1_relat_1 @ X57)
% 27.80/28.04          | (r1_tarski @ 
% 27.80/28.04             (k4_xboole_0 @ (k1_relat_1 @ X58) @ (k1_relat_1 @ X57)) @ 
% 27.80/28.04             (k1_relat_1 @ (k4_xboole_0 @ X58 @ X57)))
% 27.80/28.04          | ~ (v1_relat_1 @ X58))),
% 27.80/28.04      inference('demod', [status(thm)], ['7', '8', '9'])).
% 27.80/28.04  thf(d10_xboole_0, axiom,
% 27.80/28.04    (![A:$i,B:$i]:
% 27.80/28.04     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 27.80/28.04  thf('11', plain,
% 27.80/28.04      (![X7 : $i, X9 : $i]:
% 27.80/28.04         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 27.80/28.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.80/28.04  thf('12', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         (~ (v1_relat_1 @ X1)
% 27.80/28.04          | ~ (v1_relat_1 @ X0)
% 27.80/28.04          | ~ (r1_tarski @ (k1_relat_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 27.80/28.04               (k4_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)))
% 27.80/28.04          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ X0))
% 27.80/28.04              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0))))),
% 27.80/28.04      inference('sup-', [status(thm)], ['10', '11'])).
% 27.80/28.04  thf('13', plain,
% 27.80/28.04      ((~ (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ 
% 27.80/28.04           (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))
% 27.80/28.04        | ((k1_relat_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 27.80/28.04            = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))
% 27.80/28.04        | ~ (v1_relat_1 @ sk_B_1)
% 27.80/28.04        | ~ (v1_relat_1 @ sk_A))),
% 27.80/28.04      inference('sup-', [status(thm)], ['6', '12'])).
% 27.80/28.04  thf(d4_relat_1, axiom,
% 27.80/28.04    (![A:$i,B:$i]:
% 27.80/28.04     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 27.80/28.04       ( ![C:$i]:
% 27.80/28.04         ( ( r2_hidden @ C @ B ) <=>
% 27.80/28.04           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 27.80/28.04  thf('14', plain,
% 27.80/28.04      (![X44 : $i, X47 : $i]:
% 27.80/28.04         (((X47) = (k1_relat_1 @ X44))
% 27.80/28.04          | (r2_hidden @ 
% 27.80/28.04             (k4_tarski @ (sk_C_1 @ X47 @ X44) @ (sk_D @ X47 @ X44)) @ X44)
% 27.80/28.04          | (r2_hidden @ (sk_C_1 @ X47 @ X44) @ X47))),
% 27.80/28.04      inference('cnf', [status(esa)], [d4_relat_1])).
% 27.80/28.04  thf(t3_boole, axiom,
% 27.80/28.04    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 27.80/28.04  thf('15', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 27.80/28.04      inference('cnf', [status(esa)], [t3_boole])).
% 27.80/28.04  thf(t48_xboole_1, axiom,
% 27.80/28.04    (![A:$i,B:$i]:
% 27.80/28.04     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 27.80/28.04  thf('16', plain,
% 27.80/28.04      (![X28 : $i, X29 : $i]:
% 27.80/28.04         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 27.80/28.04           = (k3_xboole_0 @ X28 @ X29))),
% 27.80/28.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 27.80/28.04  thf('17', plain,
% 27.80/28.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 27.80/28.04      inference('sup+', [status(thm)], ['15', '16'])).
% 27.80/28.04  thf('18', plain,
% 27.80/28.04      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 27.80/28.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.80/28.04  thf('19', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 27.80/28.04      inference('simplify', [status(thm)], ['18'])).
% 27.80/28.04  thf('20', plain,
% 27.80/28.04      (![X10 : $i, X12 : $i]:
% 27.80/28.04         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 27.80/28.04          | ~ (r1_tarski @ X10 @ X12))),
% 27.80/28.04      inference('cnf', [status(esa)], [l32_xboole_1])).
% 27.80/28.04  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['19', '20'])).
% 27.80/28.04  thf('22', plain,
% 27.80/28.04      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 27.80/28.04      inference('demod', [status(thm)], ['17', '21'])).
% 27.80/28.04  thf(t4_xboole_0, axiom,
% 27.80/28.04    (![A:$i,B:$i]:
% 27.80/28.04     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 27.80/28.04            ( r1_xboole_0 @ A @ B ) ) ) & 
% 27.80/28.04       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 27.80/28.04            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 27.80/28.04  thf('23', plain,
% 27.80/28.04      (![X2 : $i, X4 : $i, X5 : $i]:
% 27.80/28.04         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 27.80/28.04          | ~ (r1_xboole_0 @ X2 @ X5))),
% 27.80/28.04      inference('cnf', [status(esa)], [t4_xboole_0])).
% 27.80/28.04  thf('24', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['22', '23'])).
% 27.80/28.04  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 27.80/28.04  thf('25', plain, (![X30 : $i]: (r1_xboole_0 @ X30 @ k1_xboole_0)),
% 27.80/28.04      inference('cnf', [status(esa)], [t65_xboole_1])).
% 27.80/28.04  thf('26', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 27.80/28.04      inference('demod', [status(thm)], ['24', '25'])).
% 27.80/28.04  thf('27', plain,
% 27.80/28.04      (![X0 : $i]:
% 27.80/28.04         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 27.80/28.04          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 27.80/28.04      inference('sup-', [status(thm)], ['14', '26'])).
% 27.80/28.04  thf('28', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 27.80/28.04      inference('demod', [status(thm)], ['24', '25'])).
% 27.80/28.04  thf('29', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['27', '28'])).
% 27.80/28.04  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 27.80/28.04  thf('30', plain, (![X19 : $i]: (r1_tarski @ k1_xboole_0 @ X19)),
% 27.80/28.04      inference('cnf', [status(esa)], [t2_xboole_1])).
% 27.80/28.04  thf('31', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['4', '5'])).
% 27.80/28.04  thf('32', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['27', '28'])).
% 27.80/28.04  thf('33', plain, ((v1_relat_1 @ sk_B_1)),
% 27.80/28.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.80/28.04  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 27.80/28.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.80/28.04  thf('35', plain,
% 27.80/28.04      (((k1_xboole_0)
% 27.80/28.04         = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))),
% 27.80/28.04      inference('demod', [status(thm)],
% 27.80/28.04                ['13', '29', '30', '31', '32', '33', '34'])).
% 27.80/28.04  thf('36', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 27.80/28.04      inference('simplify', [status(thm)], ['18'])).
% 27.80/28.04  thf(t44_xboole_1, axiom,
% 27.80/28.04    (![A:$i,B:$i,C:$i]:
% 27.80/28.04     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 27.80/28.04       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 27.80/28.04  thf('37', plain,
% 27.80/28.04      (![X25 : $i, X26 : $i, X27 : $i]:
% 27.80/28.04         ((r1_tarski @ X25 @ (k2_xboole_0 @ X26 @ X27))
% 27.80/28.04          | ~ (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27))),
% 27.80/28.04      inference('cnf', [status(esa)], [t44_xboole_1])).
% 27.80/28.04  thf('38', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 27.80/28.04      inference('sup-', [status(thm)], ['36', '37'])).
% 27.80/28.04  thf(t1_xboole_1, axiom,
% 27.80/28.04    (![A:$i,B:$i,C:$i]:
% 27.80/28.04     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 27.80/28.04       ( r1_tarski @ A @ C ) ))).
% 27.80/28.04  thf('39', plain,
% 27.80/28.04      (![X16 : $i, X17 : $i, X18 : $i]:
% 27.80/28.04         (~ (r1_tarski @ X16 @ X17)
% 27.80/28.04          | ~ (r1_tarski @ X17 @ X18)
% 27.80/28.04          | (r1_tarski @ X16 @ X18))),
% 27.80/28.04      inference('cnf', [status(esa)], [t1_xboole_1])).
% 27.80/28.04  thf('40', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.80/28.04         ((r1_tarski @ X1 @ X2)
% 27.80/28.04          | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2))),
% 27.80/28.04      inference('sup-', [status(thm)], ['38', '39'])).
% 27.80/28.04  thf('41', plain,
% 27.80/28.04      (![X0 : $i]:
% 27.80/28.04         (~ (r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_B_1) @ k1_xboole_0) @ 
% 27.80/28.04             X0)
% 27.80/28.04          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['35', '40'])).
% 27.80/28.04  thf('42', plain, (![X19 : $i]: (r1_tarski @ k1_xboole_0 @ X19)),
% 27.80/28.04      inference('cnf', [status(esa)], [t2_xboole_1])).
% 27.80/28.04  thf('43', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 27.80/28.04      inference('simplify', [status(thm)], ['18'])).
% 27.80/28.04  thf(t8_xboole_1, axiom,
% 27.80/28.04    (![A:$i,B:$i,C:$i]:
% 27.80/28.04     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 27.80/28.04       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 27.80/28.04  thf('44', plain,
% 27.80/28.04      (![X33 : $i, X34 : $i, X35 : $i]:
% 27.80/28.04         (~ (r1_tarski @ X33 @ X34)
% 27.80/28.04          | ~ (r1_tarski @ X35 @ X34)
% 27.80/28.04          | (r1_tarski @ (k2_xboole_0 @ X33 @ X35) @ X34))),
% 27.80/28.04      inference('cnf', [status(esa)], [t8_xboole_1])).
% 27.80/28.04  thf('45', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['43', '44'])).
% 27.80/28.04  thf('46', plain,
% 27.80/28.04      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 27.80/28.04      inference('sup-', [status(thm)], ['42', '45'])).
% 27.80/28.04  thf('47', plain,
% 27.80/28.04      (![X31 : $i, X32 : $i]: (r1_tarski @ X31 @ (k2_xboole_0 @ X31 @ X32))),
% 27.80/28.04      inference('cnf', [status(esa)], [t7_xboole_1])).
% 27.80/28.04  thf('48', plain,
% 27.80/28.04      (![X7 : $i, X9 : $i]:
% 27.80/28.04         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 27.80/28.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.80/28.04  thf('49', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 27.80/28.04          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 27.80/28.04      inference('sup-', [status(thm)], ['47', '48'])).
% 27.80/28.04  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['46', '49'])).
% 27.80/28.04  thf('51', plain,
% 27.80/28.04      (![X0 : $i]:
% 27.80/28.04         (~ (r1_tarski @ (k1_relat_1 @ sk_B_1) @ X0)
% 27.80/28.04          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 27.80/28.04      inference('demod', [status(thm)], ['41', '50'])).
% 27.80/28.04  thf('52', plain,
% 27.80/28.04      ((~ (v1_relat_1 @ sk_B_1)
% 27.80/28.04        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1)))),
% 27.80/28.04      inference('sup-', [status(thm)], ['3', '51'])).
% 27.80/28.04  thf('53', plain, ((v1_relat_1 @ sk_B_1)),
% 27.80/28.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.80/28.04  thf('54', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 27.80/28.04      inference('demod', [status(thm)], ['52', '53'])).
% 27.80/28.04  thf('55', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['43', '44'])).
% 27.80/28.04  thf('56', plain,
% 27.80/28.04      ((r1_tarski @ 
% 27.80/28.04        (k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)) @ 
% 27.80/28.04        (k3_relat_1 @ sk_B_1))),
% 27.80/28.04      inference('sup-', [status(thm)], ['54', '55'])).
% 27.80/28.04  thf('57', plain,
% 27.80/28.04      (![X56 : $i]:
% 27.80/28.04         (((k3_relat_1 @ X56)
% 27.80/28.04            = (k2_xboole_0 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56)))
% 27.80/28.04          | ~ (v1_relat_1 @ X56))),
% 27.80/28.04      inference('cnf', [status(esa)], [d6_relat_1])).
% 27.80/28.04  thf(commutativity_k2_xboole_0, axiom,
% 27.80/28.04    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 27.80/28.04  thf('58', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 27.80/28.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 27.80/28.04  thf('59', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 27.80/28.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 27.80/28.04  thf('60', plain,
% 27.80/28.04      (![X31 : $i, X32 : $i]: (r1_tarski @ X31 @ (k2_xboole_0 @ X31 @ X32))),
% 27.80/28.04      inference('cnf', [status(esa)], [t7_xboole_1])).
% 27.80/28.04  thf(t10_xboole_1, axiom,
% 27.80/28.04    (![A:$i,B:$i,C:$i]:
% 27.80/28.04     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 27.80/28.04  thf('61', plain,
% 27.80/28.04      (![X13 : $i, X14 : $i, X15 : $i]:
% 27.80/28.04         (~ (r1_tarski @ X13 @ X14)
% 27.80/28.04          | (r1_tarski @ X13 @ (k2_xboole_0 @ X15 @ X14)))),
% 27.80/28.04      inference('cnf', [status(esa)], [t10_xboole_1])).
% 27.80/28.04  thf('62', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.80/28.04         (r1_tarski @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 27.80/28.04      inference('sup-', [status(thm)], ['60', '61'])).
% 27.80/28.04  thf('63', plain,
% 27.80/28.04      (![X16 : $i, X17 : $i, X18 : $i]:
% 27.80/28.04         (~ (r1_tarski @ X16 @ X17)
% 27.80/28.04          | ~ (r1_tarski @ X17 @ X18)
% 27.80/28.04          | (r1_tarski @ X16 @ X18))),
% 27.80/28.04      inference('cnf', [status(esa)], [t1_xboole_1])).
% 27.80/28.04  thf('64', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.80/28.04         ((r1_tarski @ X1 @ X3)
% 27.80/28.04          | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3))),
% 27.80/28.04      inference('sup-', [status(thm)], ['62', '63'])).
% 27.80/28.04  thf('65', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.80/28.04         (~ (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ X3)
% 27.80/28.04          | (r1_tarski @ X2 @ X3))),
% 27.80/28.04      inference('sup-', [status(thm)], ['59', '64'])).
% 27.80/28.04  thf('66', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.80/28.04         (~ (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3) @ X2)
% 27.80/28.04          | (r1_tarski @ X0 @ X2))),
% 27.80/28.04      inference('sup-', [status(thm)], ['58', '65'])).
% 27.80/28.04  thf('67', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.80/28.04         (~ (r1_tarski @ (k2_xboole_0 @ (k3_relat_1 @ X0) @ X2) @ X1)
% 27.80/28.04          | ~ (v1_relat_1 @ X0)
% 27.80/28.04          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 27.80/28.04      inference('sup-', [status(thm)], ['57', '66'])).
% 27.80/28.04  thf('68', plain,
% 27.80/28.04      (((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))
% 27.80/28.04        | ~ (v1_relat_1 @ sk_B_1))),
% 27.80/28.04      inference('sup-', [status(thm)], ['56', '67'])).
% 27.80/28.04  thf('69', plain, ((v1_relat_1 @ sk_B_1)),
% 27.80/28.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.80/28.04  thf('70', plain,
% 27.80/28.04      ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))),
% 27.80/28.04      inference('demod', [status(thm)], ['68', '69'])).
% 27.80/28.04  thf('71', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['4', '5'])).
% 27.80/28.04  thf(t28_relat_1, axiom,
% 27.80/28.04    (![A:$i]:
% 27.80/28.04     ( ( v1_relat_1 @ A ) =>
% 27.80/28.04       ( ![B:$i]:
% 27.80/28.04         ( ( v1_relat_1 @ B ) =>
% 27.80/28.04           ( r1_tarski @
% 27.80/28.04             ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 27.80/28.04             ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 27.80/28.04  thf('72', plain,
% 27.80/28.04      (![X59 : $i, X60 : $i]:
% 27.80/28.04         (~ (v1_relat_1 @ X59)
% 27.80/28.04          | (r1_tarski @ 
% 27.80/28.04             (k6_subset_1 @ (k2_relat_1 @ X60) @ (k2_relat_1 @ X59)) @ 
% 27.80/28.04             (k2_relat_1 @ (k6_subset_1 @ X60 @ X59)))
% 27.80/28.04          | ~ (v1_relat_1 @ X60))),
% 27.80/28.04      inference('cnf', [status(esa)], [t28_relat_1])).
% 27.80/28.04  thf('73', plain,
% 27.80/28.04      (![X38 : $i, X39 : $i]:
% 27.80/28.04         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 27.80/28.04      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 27.80/28.04  thf('74', plain,
% 27.80/28.04      (![X38 : $i, X39 : $i]:
% 27.80/28.04         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 27.80/28.04      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 27.80/28.04  thf('75', plain,
% 27.80/28.04      (![X59 : $i, X60 : $i]:
% 27.80/28.04         (~ (v1_relat_1 @ X59)
% 27.80/28.04          | (r1_tarski @ 
% 27.80/28.04             (k4_xboole_0 @ (k2_relat_1 @ X60) @ (k2_relat_1 @ X59)) @ 
% 27.80/28.04             (k2_relat_1 @ (k4_xboole_0 @ X60 @ X59)))
% 27.80/28.04          | ~ (v1_relat_1 @ X60))),
% 27.80/28.04      inference('demod', [status(thm)], ['72', '73', '74'])).
% 27.80/28.04  thf('76', plain,
% 27.80/28.04      (![X7 : $i, X9 : $i]:
% 27.80/28.04         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 27.80/28.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.80/28.04  thf('77', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         (~ (v1_relat_1 @ X1)
% 27.80/28.04          | ~ (v1_relat_1 @ X0)
% 27.80/28.04          | ~ (r1_tarski @ (k2_relat_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 27.80/28.04               (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 27.80/28.04          | ((k2_relat_1 @ (k4_xboole_0 @ X1 @ X0))
% 27.80/28.04              = (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))))),
% 27.80/28.04      inference('sup-', [status(thm)], ['75', '76'])).
% 27.80/28.04  thf('78', plain,
% 27.80/28.04      ((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ 
% 27.80/28.04           (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))
% 27.80/28.04        | ((k2_relat_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 27.80/28.04            = (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))
% 27.80/28.04        | ~ (v1_relat_1 @ sk_B_1)
% 27.80/28.04        | ~ (v1_relat_1 @ sk_A))),
% 27.80/28.04      inference('sup-', [status(thm)], ['71', '77'])).
% 27.80/28.04  thf(d5_relat_1, axiom,
% 27.80/28.04    (![A:$i,B:$i]:
% 27.80/28.04     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 27.80/28.04       ( ![C:$i]:
% 27.80/28.04         ( ( r2_hidden @ C @ B ) <=>
% 27.80/28.04           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 27.80/28.04  thf('79', plain,
% 27.80/28.04      (![X51 : $i, X54 : $i]:
% 27.80/28.04         (((X54) = (k2_relat_1 @ X51))
% 27.80/28.04          | (r2_hidden @ 
% 27.80/28.04             (k4_tarski @ (sk_D_2 @ X54 @ X51) @ (sk_C_2 @ X54 @ X51)) @ X51)
% 27.80/28.04          | (r2_hidden @ (sk_C_2 @ X54 @ X51) @ X54))),
% 27.80/28.04      inference('cnf', [status(esa)], [d5_relat_1])).
% 27.80/28.04  thf('80', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 27.80/28.04      inference('demod', [status(thm)], ['24', '25'])).
% 27.80/28.04  thf('81', plain,
% 27.80/28.04      (![X0 : $i]:
% 27.80/28.04         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 27.80/28.04          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 27.80/28.04      inference('sup-', [status(thm)], ['79', '80'])).
% 27.80/28.04  thf('82', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 27.80/28.04      inference('demod', [status(thm)], ['24', '25'])).
% 27.80/28.04  thf('83', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['81', '82'])).
% 27.80/28.04  thf('84', plain, (![X19 : $i]: (r1_tarski @ k1_xboole_0 @ X19)),
% 27.80/28.04      inference('cnf', [status(esa)], [t2_xboole_1])).
% 27.80/28.04  thf('85', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['4', '5'])).
% 27.80/28.04  thf('86', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['81', '82'])).
% 27.80/28.04  thf('87', plain, ((v1_relat_1 @ sk_B_1)),
% 27.80/28.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.80/28.04  thf('88', plain, ((v1_relat_1 @ sk_A)),
% 27.80/28.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.80/28.04  thf('89', plain,
% 27.80/28.04      (((k1_xboole_0)
% 27.80/28.04         = (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))),
% 27.80/28.04      inference('demod', [status(thm)],
% 27.80/28.04                ['78', '83', '84', '85', '86', '87', '88'])).
% 27.80/28.04  thf('90', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.80/28.04         ((r1_tarski @ X1 @ X2)
% 27.80/28.04          | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2))),
% 27.80/28.04      inference('sup-', [status(thm)], ['38', '39'])).
% 27.80/28.04  thf('91', plain,
% 27.80/28.04      (![X0 : $i]:
% 27.80/28.04         (~ (r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_B_1) @ k1_xboole_0) @ 
% 27.80/28.04             X0)
% 27.80/28.04          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['89', '90'])).
% 27.80/28.04  thf('92', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['46', '49'])).
% 27.80/28.04  thf('93', plain,
% 27.80/28.04      (![X0 : $i]:
% 27.80/28.04         (~ (r1_tarski @ (k2_relat_1 @ sk_B_1) @ X0)
% 27.80/28.04          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0))),
% 27.80/28.04      inference('demod', [status(thm)], ['91', '92'])).
% 27.80/28.04  thf('94', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 27.80/28.04      inference('sup-', [status(thm)], ['70', '93'])).
% 27.80/28.04  thf('95', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 27.80/28.04      inference('demod', [status(thm)], ['52', '53'])).
% 27.80/28.04  thf('96', plain,
% 27.80/28.04      (![X33 : $i, X34 : $i, X35 : $i]:
% 27.80/28.04         (~ (r1_tarski @ X33 @ X34)
% 27.80/28.04          | ~ (r1_tarski @ X35 @ X34)
% 27.80/28.04          | (r1_tarski @ (k2_xboole_0 @ X33 @ X35) @ X34))),
% 27.80/28.04      inference('cnf', [status(esa)], [t8_xboole_1])).
% 27.80/28.04  thf('97', plain,
% 27.80/28.04      (![X0 : $i]:
% 27.80/28.04         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 27.80/28.04           (k3_relat_1 @ sk_B_1))
% 27.80/28.04          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B_1)))),
% 27.80/28.04      inference('sup-', [status(thm)], ['95', '96'])).
% 27.80/28.04  thf('98', plain,
% 27.80/28.04      ((r1_tarski @ 
% 27.80/28.04        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 27.80/28.04        (k3_relat_1 @ sk_B_1))),
% 27.80/28.04      inference('sup-', [status(thm)], ['94', '97'])).
% 27.80/28.04  thf('99', plain,
% 27.80/28.04      (((k1_xboole_0)
% 27.80/28.04         = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))),
% 27.80/28.04      inference('demod', [status(thm)],
% 27.80/28.04                ['13', '29', '30', '31', '32', '33', '34'])).
% 27.80/28.04  thf('100', plain,
% 27.80/28.04      (![X28 : $i, X29 : $i]:
% 27.80/28.04         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 27.80/28.04           = (k3_xboole_0 @ X28 @ X29))),
% 27.80/28.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 27.80/28.04  thf('101', plain,
% 27.80/28.04      (((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ k1_xboole_0)
% 27.80/28.04         = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))),
% 27.80/28.04      inference('sup+', [status(thm)], ['99', '100'])).
% 27.80/28.04  thf('102', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 27.80/28.04      inference('cnf', [status(esa)], [t3_boole])).
% 27.80/28.04  thf('103', plain,
% 27.80/28.04      (((k1_relat_1 @ sk_A)
% 27.80/28.04         = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))),
% 27.80/28.04      inference('demod', [status(thm)], ['101', '102'])).
% 27.80/28.04  thf('104', plain,
% 27.80/28.04      (![X0 : $i]:
% 27.80/28.04         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 27.80/28.04          | ~ (v1_relat_1 @ X0))),
% 27.80/28.04      inference('sup+', [status(thm)], ['1', '2'])).
% 27.80/28.04  thf('105', plain,
% 27.80/28.04      (![X28 : $i, X29 : $i]:
% 27.80/28.04         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 27.80/28.04           = (k3_xboole_0 @ X28 @ X29))),
% 27.80/28.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 27.80/28.04  thf('106', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 27.80/28.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 27.80/28.04  thf('107', plain,
% 27.80/28.04      (![X31 : $i, X32 : $i]: (r1_tarski @ X31 @ (k2_xboole_0 @ X31 @ X32))),
% 27.80/28.04      inference('cnf', [status(esa)], [t7_xboole_1])).
% 27.80/28.04  thf('108', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 27.80/28.04      inference('sup+', [status(thm)], ['106', '107'])).
% 27.80/28.04  thf(t43_xboole_1, axiom,
% 27.80/28.04    (![A:$i,B:$i,C:$i]:
% 27.80/28.04     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 27.80/28.04       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 27.80/28.04  thf('109', plain,
% 27.80/28.04      (![X22 : $i, X23 : $i, X24 : $i]:
% 27.80/28.04         ((r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 27.80/28.04          | ~ (r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 27.80/28.04      inference('cnf', [status(esa)], [t43_xboole_1])).
% 27.80/28.04  thf('110', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 27.80/28.04      inference('sup-', [status(thm)], ['108', '109'])).
% 27.80/28.04  thf('111', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 27.80/28.04      inference('sup+', [status(thm)], ['105', '110'])).
% 27.80/28.04  thf('112', plain,
% 27.80/28.04      (![X16 : $i, X17 : $i, X18 : $i]:
% 27.80/28.04         (~ (r1_tarski @ X16 @ X17)
% 27.80/28.04          | ~ (r1_tarski @ X17 @ X18)
% 27.80/28.04          | (r1_tarski @ X16 @ X18))),
% 27.80/28.04      inference('cnf', [status(esa)], [t1_xboole_1])).
% 27.80/28.04  thf('113', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.80/28.04         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 27.80/28.04      inference('sup-', [status(thm)], ['111', '112'])).
% 27.80/28.04  thf('114', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         (~ (v1_relat_1 @ X0)
% 27.80/28.04          | (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1) @ 
% 27.80/28.04             (k3_relat_1 @ X0)))),
% 27.80/28.04      inference('sup-', [status(thm)], ['104', '113'])).
% 27.80/28.04  thf('115', plain,
% 27.80/28.04      (((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_A))
% 27.80/28.04        | ~ (v1_relat_1 @ sk_A))),
% 27.80/28.04      inference('sup+', [status(thm)], ['103', '114'])).
% 27.80/28.04  thf('116', plain, ((v1_relat_1 @ sk_A)),
% 27.80/28.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.80/28.04  thf('117', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_A))),
% 27.80/28.04      inference('demod', [status(thm)], ['115', '116'])).
% 27.80/28.04  thf('118', plain,
% 27.80/28.04      (![X10 : $i, X12 : $i]:
% 27.80/28.04         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 27.80/28.04          | ~ (r1_tarski @ X10 @ X12))),
% 27.80/28.04      inference('cnf', [status(esa)], [l32_xboole_1])).
% 27.80/28.04  thf('119', plain,
% 27.80/28.04      (((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_A))
% 27.80/28.04         = (k1_xboole_0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['117', '118'])).
% 27.80/28.04  thf('120', plain,
% 27.80/28.04      (![X28 : $i, X29 : $i]:
% 27.80/28.04         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 27.80/28.04           = (k3_xboole_0 @ X28 @ X29))),
% 27.80/28.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 27.80/28.04  thf('121', plain,
% 27.80/28.04      (((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ k1_xboole_0)
% 27.80/28.04         = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_A)))),
% 27.80/28.04      inference('sup+', [status(thm)], ['119', '120'])).
% 27.80/28.04  thf('122', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 27.80/28.04      inference('cnf', [status(esa)], [t3_boole])).
% 27.80/28.04  thf('123', plain,
% 27.80/28.04      (((k1_relat_1 @ sk_A)
% 27.80/28.04         = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_A)))),
% 27.80/28.04      inference('demod', [status(thm)], ['121', '122'])).
% 27.80/28.04  thf('124', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 27.80/28.04      inference('sup-', [status(thm)], ['36', '37'])).
% 27.80/28.04  thf('125', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 27.80/28.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 27.80/28.04  thf('126', plain,
% 27.80/28.04      (![X22 : $i, X23 : $i, X24 : $i]:
% 27.80/28.04         ((r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 27.80/28.04          | ~ (r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 27.80/28.04      inference('cnf', [status(esa)], [t43_xboole_1])).
% 27.80/28.04  thf('127', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.80/28.04         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 27.80/28.04          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 27.80/28.04      inference('sup-', [status(thm)], ['125', '126'])).
% 27.80/28.04  thf('128', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         (r1_tarski @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 27.80/28.04      inference('sup-', [status(thm)], ['124', '127'])).
% 27.80/28.04  thf('129', plain,
% 27.80/28.04      (![X28 : $i, X29 : $i]:
% 27.80/28.04         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 27.80/28.04           = (k3_xboole_0 @ X28 @ X29))),
% 27.80/28.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 27.80/28.04  thf('130', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 27.80/28.04      inference('demod', [status(thm)], ['128', '129'])).
% 27.80/28.04  thf('131', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['43', '44'])).
% 27.80/28.04  thf('132', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         (r1_tarski @ (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X0)),
% 27.80/28.04      inference('sup-', [status(thm)], ['130', '131'])).
% 27.80/28.04  thf('133', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 27.80/28.04          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 27.80/28.04      inference('sup-', [status(thm)], ['47', '48'])).
% 27.80/28.04  thf('134', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['132', '133'])).
% 27.80/28.04  thf('135', plain,
% 27.80/28.04      (((k2_xboole_0 @ (k3_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A))
% 27.80/28.04         = (k3_relat_1 @ sk_A))),
% 27.80/28.04      inference('sup+', [status(thm)], ['123', '134'])).
% 27.80/28.04  thf('136', plain,
% 27.80/28.04      (![X56 : $i]:
% 27.80/28.04         (((k3_relat_1 @ X56)
% 27.80/28.04            = (k2_xboole_0 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56)))
% 27.80/28.04          | ~ (v1_relat_1 @ X56))),
% 27.80/28.04      inference('cnf', [status(esa)], [d6_relat_1])).
% 27.80/28.04  thf('137', plain,
% 27.80/28.04      (![X31 : $i, X32 : $i]: (r1_tarski @ X31 @ (k2_xboole_0 @ X31 @ X32))),
% 27.80/28.04      inference('cnf', [status(esa)], [t7_xboole_1])).
% 27.80/28.04  thf('138', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['43', '44'])).
% 27.80/28.04  thf('139', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ 
% 27.80/28.04          (k2_xboole_0 @ X1 @ X0))),
% 27.80/28.04      inference('sup-', [status(thm)], ['137', '138'])).
% 27.80/28.04  thf('140', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 27.80/28.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 27.80/28.04  thf('141', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         (r1_tarski @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 27.80/28.04          (k2_xboole_0 @ X1 @ X0))),
% 27.80/28.04      inference('demod', [status(thm)], ['139', '140'])).
% 27.80/28.04  thf('142', plain,
% 27.80/28.04      (![X0 : $i]:
% 27.80/28.04         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0)) @ 
% 27.80/28.04           (k2_xboole_0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 27.80/28.04          | ~ (v1_relat_1 @ X0))),
% 27.80/28.04      inference('sup+', [status(thm)], ['136', '141'])).
% 27.80/28.04  thf('143', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 27.80/28.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 27.80/28.04  thf('144', plain,
% 27.80/28.04      (![X0 : $i]:
% 27.80/28.04         ((r1_tarski @ (k2_xboole_0 @ (k3_relat_1 @ X0) @ (k1_relat_1 @ X0)) @ 
% 27.80/28.04           (k2_xboole_0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 27.80/28.04          | ~ (v1_relat_1 @ X0))),
% 27.80/28.04      inference('demod', [status(thm)], ['142', '143'])).
% 27.80/28.04  thf('145', plain,
% 27.80/28.04      (((r1_tarski @ (k3_relat_1 @ sk_A) @ 
% 27.80/28.04         (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 27.80/28.04        | ~ (v1_relat_1 @ sk_A))),
% 27.80/28.04      inference('sup+', [status(thm)], ['135', '144'])).
% 27.80/28.04  thf('146', plain, ((v1_relat_1 @ sk_A)),
% 27.80/28.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.80/28.04  thf('147', plain,
% 27.80/28.04      ((r1_tarski @ (k3_relat_1 @ sk_A) @ 
% 27.80/28.04        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 27.80/28.04      inference('demod', [status(thm)], ['145', '146'])).
% 27.80/28.04  thf('148', plain,
% 27.80/28.04      (![X7 : $i, X9 : $i]:
% 27.80/28.04         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 27.80/28.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.80/28.04  thf('149', plain,
% 27.80/28.04      ((~ (r1_tarski @ 
% 27.80/28.04           (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 27.80/28.04           (k3_relat_1 @ sk_A))
% 27.80/28.04        | ((k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 27.80/28.04            = (k3_relat_1 @ sk_A)))),
% 27.80/28.04      inference('sup-', [status(thm)], ['147', '148'])).
% 27.80/28.04  thf('150', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_A))),
% 27.80/28.04      inference('demod', [status(thm)], ['115', '116'])).
% 27.80/28.04  thf('151', plain,
% 27.80/28.04      (![X56 : $i]:
% 27.80/28.04         (((k3_relat_1 @ X56)
% 27.80/28.04            = (k2_xboole_0 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56)))
% 27.80/28.04          | ~ (v1_relat_1 @ X56))),
% 27.80/28.04      inference('cnf', [status(esa)], [d6_relat_1])).
% 27.80/28.04  thf('152', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 27.80/28.04      inference('sup+', [status(thm)], ['106', '107'])).
% 27.80/28.04  thf('153', plain,
% 27.80/28.04      (![X0 : $i]:
% 27.80/28.04         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 27.80/28.04          | ~ (v1_relat_1 @ X0))),
% 27.80/28.04      inference('sup+', [status(thm)], ['151', '152'])).
% 27.80/28.04  thf('154', plain,
% 27.80/28.04      (![X33 : $i, X34 : $i, X35 : $i]:
% 27.80/28.04         (~ (r1_tarski @ X33 @ X34)
% 27.80/28.04          | ~ (r1_tarski @ X35 @ X34)
% 27.80/28.04          | (r1_tarski @ (k2_xboole_0 @ X33 @ X35) @ X34))),
% 27.80/28.04      inference('cnf', [status(esa)], [t8_xboole_1])).
% 27.80/28.04  thf('155', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]:
% 27.80/28.04         (~ (v1_relat_1 @ X0)
% 27.80/28.04          | (r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ X0) @ X1) @ 
% 27.80/28.04             (k3_relat_1 @ X0))
% 27.80/28.04          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0)))),
% 27.80/28.04      inference('sup-', [status(thm)], ['153', '154'])).
% 27.80/28.04  thf('156', plain,
% 27.80/28.04      (((r1_tarski @ 
% 27.80/28.04         (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 27.80/28.04         (k3_relat_1 @ sk_A))
% 27.80/28.04        | ~ (v1_relat_1 @ sk_A))),
% 27.80/28.04      inference('sup-', [status(thm)], ['150', '155'])).
% 27.80/28.04  thf('157', plain,
% 27.80/28.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 27.80/28.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 27.80/28.04  thf('158', plain, ((v1_relat_1 @ sk_A)),
% 27.80/28.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.80/28.04  thf('159', plain,
% 27.80/28.04      ((r1_tarski @ 
% 27.80/28.04        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 27.80/28.04        (k3_relat_1 @ sk_A))),
% 27.80/28.04      inference('demod', [status(thm)], ['156', '157', '158'])).
% 27.80/28.04  thf('160', plain,
% 27.80/28.04      (((k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 27.80/28.04         = (k3_relat_1 @ sk_A))),
% 27.80/28.04      inference('demod', [status(thm)], ['149', '159'])).
% 27.80/28.04  thf('161', plain,
% 27.80/28.04      ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 27.80/28.04      inference('demod', [status(thm)], ['98', '160'])).
% 27.80/28.04  thf('162', plain, ($false), inference('demod', [status(thm)], ['0', '161'])).
% 27.80/28.04  
% 27.80/28.04  % SZS output end Refutation
% 27.80/28.04  
% 27.80/28.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
