%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MfWZWmI07q

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:56 EST 2020

% Result     : Theorem 2.37s
% Output     : Refutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 361 expanded)
%              Number of leaves         :   39 ( 129 expanded)
%              Depth                    :   26
%              Number of atoms          :  924 (2657 expanded)
%              Number of equality atoms :   43 ( 148 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_tarski @ X29 @ X28 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X45 ) @ ( k1_relat_1 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X45 ) @ ( k1_relat_1 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['1','6'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('10',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k2_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ X47 ) @ ( k1_relat_1 @ X46 ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ X47 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t15_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k6_subset_1 @ X34 @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k6_subset_1 @ X34 @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X47 ) @ ( k1_relat_1 @ X46 ) ) @ ( k1_relat_1 @ ( k4_xboole_0 @ X47 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('26',plain,(
    ! [X40: $i,X43: $i] :
      ( ( X43
        = ( k1_relat_1 @ X40 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X43 @ X40 ) @ ( sk_D_1 @ X43 @ X40 ) ) @ X40 )
      | ( r2_hidden @ ( sk_C_1 @ X43 @ X40 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('27',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('35',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('38',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['25','38'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('41',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('42',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['43'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('45',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_tarski @ X27 @ X26 )
      | ( r1_tarski @ ( k2_xboole_0 @ X25 @ X27 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('49',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
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
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['41','51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k2_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['8','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('59',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('61',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('63',plain,(
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X45 ) @ ( k1_relat_1 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['1','6'])).

thf('64',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k2_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k3_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_xboole_0 @ ( k3_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['61','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('73',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_B_1 ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('75',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_B_1 ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('77',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_tarski @ X27 @ X26 )
      | ( r1_tarski @ ( k2_xboole_0 @ X25 @ X27 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('82',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k2_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['80','85'])).

thf(t26_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('87',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X49 @ X48 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X49 ) @ ( k2_relat_1 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf('88',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k2_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['75','95'])).

thf('97',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('98',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_tarski @ X27 @ X26 )
      | ( r1_tarski @ ( k2_xboole_0 @ X25 @ X27 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B_1 ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('102',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['0','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MfWZWmI07q
% 0.15/0.34  % Computer   : n013.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 14:26:10 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 2.37/2.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.37/2.56  % Solved by: fo/fo7.sh
% 2.37/2.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.37/2.56  % done 3731 iterations in 2.106s
% 2.37/2.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.37/2.56  % SZS output start Refutation
% 2.37/2.56  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 2.37/2.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.37/2.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.37/2.56  thf(sk_B_type, type, sk_B: $i > $i).
% 2.37/2.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.37/2.56  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 2.37/2.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.37/2.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.37/2.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.37/2.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.37/2.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.37/2.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.37/2.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.37/2.56  thf(sk_A_type, type, sk_A: $i).
% 2.37/2.56  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.37/2.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.37/2.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.37/2.56  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 2.37/2.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.37/2.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.37/2.56  thf(t31_relat_1, conjecture,
% 2.37/2.56    (![A:$i]:
% 2.37/2.56     ( ( v1_relat_1 @ A ) =>
% 2.37/2.56       ( ![B:$i]:
% 2.37/2.56         ( ( v1_relat_1 @ B ) =>
% 2.37/2.56           ( ( r1_tarski @ A @ B ) =>
% 2.37/2.56             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 2.37/2.56  thf(zf_stmt_0, negated_conjecture,
% 2.37/2.56    (~( ![A:$i]:
% 2.37/2.56        ( ( v1_relat_1 @ A ) =>
% 2.37/2.56          ( ![B:$i]:
% 2.37/2.56            ( ( v1_relat_1 @ B ) =>
% 2.37/2.56              ( ( r1_tarski @ A @ B ) =>
% 2.37/2.56                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 2.37/2.56    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 2.37/2.56  thf('0', plain,
% 2.37/2.56      (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 2.37/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.56  thf(d6_relat_1, axiom,
% 2.37/2.56    (![A:$i]:
% 2.37/2.56     ( ( v1_relat_1 @ A ) =>
% 2.37/2.56       ( ( k3_relat_1 @ A ) =
% 2.37/2.56         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 2.37/2.56  thf('1', plain,
% 2.37/2.56      (![X45 : $i]:
% 2.37/2.56         (((k3_relat_1 @ X45)
% 2.37/2.56            = (k2_xboole_0 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45)))
% 2.37/2.56          | ~ (v1_relat_1 @ X45))),
% 2.37/2.56      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.37/2.56  thf(commutativity_k2_tarski, axiom,
% 2.37/2.56    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.37/2.56  thf('2', plain,
% 2.37/2.56      (![X28 : $i, X29 : $i]:
% 2.37/2.56         ((k2_tarski @ X29 @ X28) = (k2_tarski @ X28 @ X29))),
% 2.37/2.56      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.37/2.56  thf(l51_zfmisc_1, axiom,
% 2.37/2.56    (![A:$i,B:$i]:
% 2.37/2.56     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.37/2.56  thf('3', plain,
% 2.37/2.56      (![X32 : $i, X33 : $i]:
% 2.37/2.56         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 2.37/2.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.37/2.56  thf('4', plain,
% 2.37/2.56      (![X0 : $i, X1 : $i]:
% 2.37/2.56         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 2.37/2.56      inference('sup+', [status(thm)], ['2', '3'])).
% 2.37/2.56  thf('5', plain,
% 2.37/2.56      (![X32 : $i, X33 : $i]:
% 2.37/2.56         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 2.37/2.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.37/2.56  thf('6', plain,
% 2.37/2.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.37/2.56      inference('sup+', [status(thm)], ['4', '5'])).
% 2.37/2.56  thf('7', plain,
% 2.37/2.56      (![X45 : $i]:
% 2.37/2.56         (((k3_relat_1 @ X45)
% 2.37/2.56            = (k2_xboole_0 @ (k2_relat_1 @ X45) @ (k1_relat_1 @ X45)))
% 2.37/2.56          | ~ (v1_relat_1 @ X45))),
% 2.37/2.56      inference('demod', [status(thm)], ['1', '6'])).
% 2.37/2.56  thf('8', plain,
% 2.37/2.56      (![X45 : $i]:
% 2.37/2.56         (((k3_relat_1 @ X45)
% 2.37/2.56            = (k2_xboole_0 @ (k2_relat_1 @ X45) @ (k1_relat_1 @ X45)))
% 2.37/2.56          | ~ (v1_relat_1 @ X45))),
% 2.37/2.56      inference('demod', [status(thm)], ['1', '6'])).
% 2.37/2.56  thf('9', plain,
% 2.37/2.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.37/2.56      inference('sup+', [status(thm)], ['4', '5'])).
% 2.37/2.56  thf('10', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 2.37/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.56  thf(t10_xboole_1, axiom,
% 2.37/2.56    (![A:$i,B:$i,C:$i]:
% 2.37/2.56     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 2.37/2.56  thf('11', plain,
% 2.37/2.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.37/2.56         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ X8 @ (k2_xboole_0 @ X10 @ X9)))),
% 2.37/2.56      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.37/2.56  thf('12', plain,
% 2.37/2.56      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ sk_B_1))),
% 2.37/2.56      inference('sup-', [status(thm)], ['10', '11'])).
% 2.37/2.56  thf('13', plain,
% 2.37/2.56      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0))),
% 2.37/2.56      inference('sup+', [status(thm)], ['9', '12'])).
% 2.37/2.56  thf(t43_xboole_1, axiom,
% 2.37/2.56    (![A:$i,B:$i,C:$i]:
% 2.37/2.56     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 2.37/2.56       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 2.37/2.56  thf('14', plain,
% 2.37/2.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.37/2.56         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 2.37/2.56          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 2.37/2.56      inference('cnf', [status(esa)], [t43_xboole_1])).
% 2.37/2.56  thf('15', plain,
% 2.37/2.56      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B_1) @ X0)),
% 2.37/2.56      inference('sup-', [status(thm)], ['13', '14'])).
% 2.37/2.56  thf(t3_xboole_1, axiom,
% 2.37/2.56    (![A:$i]:
% 2.37/2.56     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.37/2.56  thf('16', plain,
% 2.37/2.56      (![X15 : $i]:
% 2.37/2.56         (((X15) = (k1_xboole_0)) | ~ (r1_tarski @ X15 @ k1_xboole_0))),
% 2.37/2.56      inference('cnf', [status(esa)], [t3_xboole_1])).
% 2.37/2.56  thf('17', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 2.37/2.56      inference('sup-', [status(thm)], ['15', '16'])).
% 2.37/2.56  thf(t15_relat_1, axiom,
% 2.37/2.56    (![A:$i]:
% 2.37/2.56     ( ( v1_relat_1 @ A ) =>
% 2.37/2.56       ( ![B:$i]:
% 2.37/2.56         ( ( v1_relat_1 @ B ) =>
% 2.37/2.56           ( r1_tarski @
% 2.37/2.56             ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ 
% 2.37/2.56             ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 2.37/2.56  thf('18', plain,
% 2.37/2.56      (![X46 : $i, X47 : $i]:
% 2.37/2.56         (~ (v1_relat_1 @ X46)
% 2.37/2.56          | (r1_tarski @ 
% 2.37/2.56             (k6_subset_1 @ (k1_relat_1 @ X47) @ (k1_relat_1 @ X46)) @ 
% 2.37/2.56             (k1_relat_1 @ (k6_subset_1 @ X47 @ X46)))
% 2.37/2.56          | ~ (v1_relat_1 @ X47))),
% 2.37/2.56      inference('cnf', [status(esa)], [t15_relat_1])).
% 2.37/2.56  thf(redefinition_k6_subset_1, axiom,
% 2.37/2.56    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.37/2.56  thf('19', plain,
% 2.37/2.56      (![X34 : $i, X35 : $i]:
% 2.37/2.56         ((k6_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))),
% 2.37/2.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.37/2.56  thf('20', plain,
% 2.37/2.56      (![X34 : $i, X35 : $i]:
% 2.37/2.56         ((k6_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))),
% 2.37/2.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.37/2.56  thf('21', plain,
% 2.37/2.56      (![X46 : $i, X47 : $i]:
% 2.37/2.56         (~ (v1_relat_1 @ X46)
% 2.37/2.56          | (r1_tarski @ 
% 2.37/2.56             (k4_xboole_0 @ (k1_relat_1 @ X47) @ (k1_relat_1 @ X46)) @ 
% 2.37/2.56             (k1_relat_1 @ (k4_xboole_0 @ X47 @ X46)))
% 2.37/2.56          | ~ (v1_relat_1 @ X47))),
% 2.37/2.56      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.37/2.56  thf('22', plain,
% 2.37/2.56      (((r1_tarski @ 
% 2.37/2.56         (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)) @ 
% 2.37/2.56         (k1_relat_1 @ k1_xboole_0))
% 2.37/2.56        | ~ (v1_relat_1 @ sk_A)
% 2.37/2.56        | ~ (v1_relat_1 @ sk_B_1))),
% 2.37/2.56      inference('sup+', [status(thm)], ['17', '21'])).
% 2.37/2.56  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 2.37/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.56  thf('24', plain, ((v1_relat_1 @ sk_B_1)),
% 2.37/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.56  thf('25', plain,
% 2.37/2.56      ((r1_tarski @ 
% 2.37/2.56        (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)) @ 
% 2.37/2.56        (k1_relat_1 @ k1_xboole_0))),
% 2.37/2.56      inference('demod', [status(thm)], ['22', '23', '24'])).
% 2.37/2.56  thf(d4_relat_1, axiom,
% 2.37/2.56    (![A:$i,B:$i]:
% 2.37/2.56     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 2.37/2.56       ( ![C:$i]:
% 2.37/2.56         ( ( r2_hidden @ C @ B ) <=>
% 2.37/2.56           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 2.37/2.56  thf('26', plain,
% 2.37/2.56      (![X40 : $i, X43 : $i]:
% 2.37/2.56         (((X43) = (k1_relat_1 @ X40))
% 2.37/2.56          | (r2_hidden @ 
% 2.37/2.56             (k4_tarski @ (sk_C_1 @ X43 @ X40) @ (sk_D_1 @ X43 @ X40)) @ X40)
% 2.37/2.56          | (r2_hidden @ (sk_C_1 @ X43 @ X40) @ X43))),
% 2.37/2.56      inference('cnf', [status(esa)], [d4_relat_1])).
% 2.37/2.56  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 2.37/2.56  thf('27', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 2.37/2.56      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.37/2.56  thf(t7_xboole_0, axiom,
% 2.37/2.56    (![A:$i]:
% 2.37/2.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.37/2.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.37/2.56  thf('28', plain,
% 2.37/2.56      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 2.37/2.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.37/2.56  thf(t4_xboole_0, axiom,
% 2.37/2.56    (![A:$i,B:$i]:
% 2.37/2.56     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.37/2.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.37/2.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.37/2.56            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.37/2.56  thf('29', plain,
% 2.37/2.56      (![X0 : $i, X2 : $i, X3 : $i]:
% 2.37/2.56         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 2.37/2.56          | ~ (r1_xboole_0 @ X0 @ X3))),
% 2.37/2.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.37/2.56  thf('30', plain,
% 2.37/2.56      (![X0 : $i, X1 : $i]:
% 2.37/2.56         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.37/2.56      inference('sup-', [status(thm)], ['28', '29'])).
% 2.37/2.56  thf('31', plain,
% 2.37/2.56      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.37/2.56      inference('sup-', [status(thm)], ['27', '30'])).
% 2.37/2.56  thf('32', plain,
% 2.37/2.56      (![X0 : $i, X2 : $i, X3 : $i]:
% 2.37/2.56         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 2.37/2.56          | ~ (r1_xboole_0 @ X0 @ X3))),
% 2.37/2.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.37/2.56  thf('33', plain,
% 2.37/2.56      (![X0 : $i, X1 : $i]:
% 2.37/2.56         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 2.37/2.56      inference('sup-', [status(thm)], ['31', '32'])).
% 2.37/2.56  thf('34', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 2.37/2.56      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.37/2.56  thf('35', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 2.37/2.56      inference('demod', [status(thm)], ['33', '34'])).
% 2.37/2.56  thf('36', plain,
% 2.37/2.56      (![X0 : $i]:
% 2.37/2.56         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 2.37/2.56          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 2.37/2.56      inference('sup-', [status(thm)], ['26', '35'])).
% 2.37/2.56  thf('37', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 2.37/2.56      inference('demod', [status(thm)], ['33', '34'])).
% 2.37/2.56  thf('38', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.37/2.56      inference('sup-', [status(thm)], ['36', '37'])).
% 2.37/2.56  thf('39', plain,
% 2.37/2.56      ((r1_tarski @ 
% 2.37/2.56        (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)) @ 
% 2.37/2.56        k1_xboole_0)),
% 2.37/2.56      inference('demod', [status(thm)], ['25', '38'])).
% 2.37/2.56  thf(t44_xboole_1, axiom,
% 2.37/2.56    (![A:$i,B:$i,C:$i]:
% 2.37/2.56     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 2.37/2.56       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.37/2.56  thf('40', plain,
% 2.37/2.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.37/2.56         ((r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 2.37/2.56          | ~ (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21))),
% 2.37/2.56      inference('cnf', [status(esa)], [t44_xboole_1])).
% 2.37/2.56  thf('41', plain,
% 2.37/2.56      ((r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 2.37/2.56        (k2_xboole_0 @ (k1_relat_1 @ sk_B_1) @ k1_xboole_0))),
% 2.37/2.56      inference('sup-', [status(thm)], ['39', '40'])).
% 2.37/2.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.37/2.56  thf('42', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 2.37/2.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.37/2.56  thf(d10_xboole_0, axiom,
% 2.37/2.56    (![A:$i,B:$i]:
% 2.37/2.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.37/2.56  thf('43', plain,
% 2.37/2.56      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 2.37/2.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.37/2.56  thf('44', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 2.37/2.56      inference('simplify', [status(thm)], ['43'])).
% 2.37/2.56  thf(t8_xboole_1, axiom,
% 2.37/2.56    (![A:$i,B:$i,C:$i]:
% 2.37/2.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.37/2.56       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.37/2.56  thf('45', plain,
% 2.37/2.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.37/2.56         (~ (r1_tarski @ X25 @ X26)
% 2.37/2.56          | ~ (r1_tarski @ X27 @ X26)
% 2.37/2.56          | (r1_tarski @ (k2_xboole_0 @ X25 @ X27) @ X26))),
% 2.37/2.56      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.37/2.56  thf('46', plain,
% 2.37/2.56      (![X0 : $i, X1 : $i]:
% 2.37/2.56         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 2.37/2.56      inference('sup-', [status(thm)], ['44', '45'])).
% 2.37/2.56  thf('47', plain,
% 2.37/2.56      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 2.37/2.56      inference('sup-', [status(thm)], ['42', '46'])).
% 2.37/2.56  thf(t7_xboole_1, axiom,
% 2.37/2.56    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.37/2.56  thf('48', plain,
% 2.37/2.56      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 2.37/2.56      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.37/2.56  thf('49', plain,
% 2.37/2.56      (![X5 : $i, X7 : $i]:
% 2.37/2.56         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 2.37/2.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.37/2.56  thf('50', plain,
% 2.37/2.56      (![X0 : $i, X1 : $i]:
% 2.37/2.56         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 2.37/2.56          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 2.37/2.56      inference('sup-', [status(thm)], ['48', '49'])).
% 2.37/2.56  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.37/2.56      inference('sup-', [status(thm)], ['47', '50'])).
% 2.37/2.56  thf('52', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1))),
% 2.37/2.56      inference('demod', [status(thm)], ['41', '51'])).
% 2.37/2.56  thf('53', plain,
% 2.37/2.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.37/2.56         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ X8 @ (k2_xboole_0 @ X10 @ X9)))),
% 2.37/2.56      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.37/2.56  thf('54', plain,
% 2.37/2.56      (![X0 : $i]:
% 2.37/2.56         (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 2.37/2.56          (k2_xboole_0 @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 2.37/2.56      inference('sup-', [status(thm)], ['52', '53'])).
% 2.37/2.56  thf('55', plain,
% 2.37/2.56      (((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))
% 2.37/2.56        | ~ (v1_relat_1 @ sk_B_1))),
% 2.37/2.56      inference('sup+', [status(thm)], ['8', '54'])).
% 2.37/2.56  thf('56', plain, ((v1_relat_1 @ sk_B_1)),
% 2.37/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.56  thf('57', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 2.37/2.56      inference('demod', [status(thm)], ['55', '56'])).
% 2.37/2.56  thf('58', plain,
% 2.37/2.56      (![X0 : $i, X1 : $i]:
% 2.37/2.56         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 2.37/2.56      inference('sup-', [status(thm)], ['44', '45'])).
% 2.37/2.56  thf('59', plain,
% 2.37/2.56      ((r1_tarski @ 
% 2.37/2.56        (k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)) @ 
% 2.37/2.56        (k3_relat_1 @ sk_B_1))),
% 2.37/2.56      inference('sup-', [status(thm)], ['57', '58'])).
% 2.37/2.57  thf('60', plain,
% 2.37/2.57      (![X0 : $i, X1 : $i]:
% 2.37/2.57         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 2.37/2.57          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 2.37/2.57      inference('sup-', [status(thm)], ['48', '49'])).
% 2.37/2.57  thf('61', plain,
% 2.37/2.57      (((k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))
% 2.37/2.57         = (k3_relat_1 @ sk_B_1))),
% 2.37/2.57      inference('sup-', [status(thm)], ['59', '60'])).
% 2.37/2.57  thf('62', plain,
% 2.37/2.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.37/2.57      inference('sup+', [status(thm)], ['4', '5'])).
% 2.37/2.57  thf('63', plain,
% 2.37/2.57      (![X45 : $i]:
% 2.37/2.57         (((k3_relat_1 @ X45)
% 2.37/2.57            = (k2_xboole_0 @ (k2_relat_1 @ X45) @ (k1_relat_1 @ X45)))
% 2.37/2.57          | ~ (v1_relat_1 @ X45))),
% 2.37/2.57      inference('demod', [status(thm)], ['1', '6'])).
% 2.37/2.57  thf('64', plain,
% 2.37/2.57      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 2.37/2.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.37/2.57  thf('65', plain,
% 2.37/2.57      (![X0 : $i]:
% 2.37/2.57         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 2.37/2.57          | ~ (v1_relat_1 @ X0))),
% 2.37/2.57      inference('sup+', [status(thm)], ['63', '64'])).
% 2.37/2.57  thf('66', plain,
% 2.37/2.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.37/2.57         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ X8 @ (k2_xboole_0 @ X10 @ X9)))),
% 2.37/2.57      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.37/2.57  thf('67', plain,
% 2.37/2.57      (![X0 : $i, X1 : $i]:
% 2.37/2.57         (~ (v1_relat_1 @ X0)
% 2.37/2.57          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 2.37/2.57             (k2_xboole_0 @ X1 @ (k3_relat_1 @ X0))))),
% 2.37/2.57      inference('sup-', [status(thm)], ['65', '66'])).
% 2.37/2.57  thf('68', plain,
% 2.37/2.57      (![X0 : $i, X1 : $i]:
% 2.37/2.57         ((r1_tarski @ (k2_relat_1 @ X1) @ 
% 2.37/2.57           (k2_xboole_0 @ (k3_relat_1 @ X1) @ X0))
% 2.37/2.57          | ~ (v1_relat_1 @ X1))),
% 2.37/2.57      inference('sup+', [status(thm)], ['62', '67'])).
% 2.37/2.57  thf('69', plain,
% 2.37/2.57      (((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))
% 2.37/2.57        | ~ (v1_relat_1 @ sk_B_1))),
% 2.37/2.57      inference('sup+', [status(thm)], ['61', '68'])).
% 2.37/2.57  thf('70', plain, ((v1_relat_1 @ sk_B_1)),
% 2.37/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.57  thf('71', plain,
% 2.37/2.57      ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))),
% 2.37/2.57      inference('demod', [status(thm)], ['69', '70'])).
% 2.37/2.57  thf('72', plain,
% 2.37/2.57      (![X0 : $i, X1 : $i]:
% 2.37/2.57         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 2.37/2.57      inference('sup-', [status(thm)], ['44', '45'])).
% 2.37/2.57  thf('73', plain,
% 2.37/2.57      ((r1_tarski @ 
% 2.37/2.57        (k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_B_1)) @ 
% 2.37/2.57        (k3_relat_1 @ sk_B_1))),
% 2.37/2.57      inference('sup-', [status(thm)], ['71', '72'])).
% 2.37/2.57  thf('74', plain,
% 2.37/2.57      (![X0 : $i, X1 : $i]:
% 2.37/2.57         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 2.37/2.57          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 2.37/2.57      inference('sup-', [status(thm)], ['48', '49'])).
% 2.37/2.57  thf('75', plain,
% 2.37/2.57      (((k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_B_1))
% 2.37/2.57         = (k3_relat_1 @ sk_B_1))),
% 2.37/2.57      inference('sup-', [status(thm)], ['73', '74'])).
% 2.37/2.57  thf('76', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 2.37/2.57      inference('simplify', [status(thm)], ['43'])).
% 2.37/2.57  thf('77', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 2.37/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.57  thf('78', plain,
% 2.37/2.57      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.37/2.57         (~ (r1_tarski @ X25 @ X26)
% 2.37/2.57          | ~ (r1_tarski @ X27 @ X26)
% 2.37/2.57          | (r1_tarski @ (k2_xboole_0 @ X25 @ X27) @ X26))),
% 2.37/2.57      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.37/2.57  thf('79', plain,
% 2.37/2.57      (![X0 : $i]:
% 2.37/2.57         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 2.37/2.57          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 2.37/2.57      inference('sup-', [status(thm)], ['77', '78'])).
% 2.37/2.57  thf('80', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_B_1)),
% 2.37/2.57      inference('sup-', [status(thm)], ['76', '79'])).
% 2.37/2.57  thf('81', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 2.37/2.57      inference('simplify', [status(thm)], ['43'])).
% 2.37/2.57  thf('82', plain,
% 2.37/2.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.37/2.57         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ X8 @ (k2_xboole_0 @ X10 @ X9)))),
% 2.37/2.57      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.37/2.57  thf('83', plain,
% 2.37/2.57      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.37/2.57      inference('sup-', [status(thm)], ['81', '82'])).
% 2.37/2.57  thf('84', plain,
% 2.37/2.57      (![X5 : $i, X7 : $i]:
% 2.37/2.57         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 2.37/2.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.37/2.57  thf('85', plain,
% 2.37/2.57      (![X0 : $i, X1 : $i]:
% 2.37/2.57         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 2.37/2.57          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 2.37/2.57      inference('sup-', [status(thm)], ['83', '84'])).
% 2.37/2.57  thf('86', plain, (((k2_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 2.37/2.57      inference('sup-', [status(thm)], ['80', '85'])).
% 2.37/2.57  thf(t26_relat_1, axiom,
% 2.37/2.57    (![A:$i]:
% 2.37/2.57     ( ( v1_relat_1 @ A ) =>
% 2.37/2.57       ( ![B:$i]:
% 2.37/2.57         ( ( v1_relat_1 @ B ) =>
% 2.37/2.57           ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 2.37/2.57             ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 2.37/2.57  thf('87', plain,
% 2.37/2.57      (![X48 : $i, X49 : $i]:
% 2.37/2.57         (~ (v1_relat_1 @ X48)
% 2.37/2.57          | ((k2_relat_1 @ (k2_xboole_0 @ X49 @ X48))
% 2.37/2.57              = (k2_xboole_0 @ (k2_relat_1 @ X49) @ (k2_relat_1 @ X48)))
% 2.37/2.57          | ~ (v1_relat_1 @ X49))),
% 2.37/2.57      inference('cnf', [status(esa)], [t26_relat_1])).
% 2.37/2.57  thf('88', plain,
% 2.37/2.57      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 2.37/2.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.37/2.57  thf('89', plain,
% 2.37/2.57      (![X0 : $i, X1 : $i]:
% 2.37/2.57         ((r1_tarski @ (k2_relat_1 @ X1) @ 
% 2.37/2.57           (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 2.37/2.57          | ~ (v1_relat_1 @ X1)
% 2.37/2.57          | ~ (v1_relat_1 @ X0))),
% 2.37/2.57      inference('sup+', [status(thm)], ['87', '88'])).
% 2.37/2.57  thf('90', plain,
% 2.37/2.57      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 2.37/2.57        | ~ (v1_relat_1 @ sk_B_1)
% 2.37/2.57        | ~ (v1_relat_1 @ sk_A))),
% 2.37/2.57      inference('sup+', [status(thm)], ['86', '89'])).
% 2.37/2.57  thf('91', plain, ((v1_relat_1 @ sk_B_1)),
% 2.37/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.57  thf('92', plain, ((v1_relat_1 @ sk_A)),
% 2.37/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.57  thf('93', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 2.37/2.57      inference('demod', [status(thm)], ['90', '91', '92'])).
% 2.37/2.57  thf('94', plain,
% 2.37/2.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.37/2.57         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ X8 @ (k2_xboole_0 @ X10 @ X9)))),
% 2.37/2.57      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.37/2.57  thf('95', plain,
% 2.37/2.57      (![X0 : $i]:
% 2.37/2.57         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 2.37/2.57          (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_B_1)))),
% 2.37/2.57      inference('sup-', [status(thm)], ['93', '94'])).
% 2.37/2.57  thf('96', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 2.37/2.57      inference('sup+', [status(thm)], ['75', '95'])).
% 2.37/2.57  thf('97', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 2.37/2.57      inference('demod', [status(thm)], ['55', '56'])).
% 2.37/2.57  thf('98', plain,
% 2.37/2.57      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.37/2.57         (~ (r1_tarski @ X25 @ X26)
% 2.37/2.57          | ~ (r1_tarski @ X27 @ X26)
% 2.37/2.57          | (r1_tarski @ (k2_xboole_0 @ X25 @ X27) @ X26))),
% 2.37/2.57      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.37/2.57  thf('99', plain,
% 2.37/2.57      (![X0 : $i]:
% 2.37/2.57         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 2.37/2.57           (k3_relat_1 @ sk_B_1))
% 2.37/2.57          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B_1)))),
% 2.37/2.57      inference('sup-', [status(thm)], ['97', '98'])).
% 2.37/2.57  thf('100', plain,
% 2.37/2.57      ((r1_tarski @ 
% 2.37/2.57        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 2.37/2.57        (k3_relat_1 @ sk_B_1))),
% 2.37/2.57      inference('sup-', [status(thm)], ['96', '99'])).
% 2.37/2.57  thf('101', plain,
% 2.37/2.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.37/2.57      inference('sup+', [status(thm)], ['4', '5'])).
% 2.37/2.57  thf('102', plain,
% 2.37/2.57      ((r1_tarski @ 
% 2.37/2.57        (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 2.37/2.57        (k3_relat_1 @ sk_B_1))),
% 2.37/2.57      inference('demod', [status(thm)], ['100', '101'])).
% 2.37/2.57  thf('103', plain,
% 2.37/2.57      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))
% 2.37/2.57        | ~ (v1_relat_1 @ sk_A))),
% 2.37/2.57      inference('sup+', [status(thm)], ['7', '102'])).
% 2.37/2.57  thf('104', plain, ((v1_relat_1 @ sk_A)),
% 2.37/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.57  thf('105', plain,
% 2.37/2.57      ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 2.37/2.57      inference('demod', [status(thm)], ['103', '104'])).
% 2.37/2.57  thf('106', plain, ($false), inference('demod', [status(thm)], ['0', '105'])).
% 2.37/2.57  
% 2.37/2.57  % SZS output end Refutation
% 2.37/2.57  
% 2.37/2.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
