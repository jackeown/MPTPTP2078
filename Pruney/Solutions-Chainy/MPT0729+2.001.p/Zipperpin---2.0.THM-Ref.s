%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JxJ7qiQd50

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:40 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 330 expanded)
%              Number of leaves         :   33 ( 113 expanded)
%              Depth                    :   17
%              Number of atoms          : 1051 (2432 expanded)
%              Number of equality atoms :   87 ( 226 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('0',plain,(
    ! [X61: $i] :
      ( ( k1_ordinal1 @ X61 )
      = ( k2_xboole_0 @ X61 @ ( k1_tarski @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_tarski @ X35 @ X34 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_tarski @ X35 @ X34 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X59 @ X60 ) )
      = ( k3_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X59 @ X60 ) )
      = ( k3_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_ordinal1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t12_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k1_ordinal1 @ A )
        = ( k1_ordinal1 @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k1_ordinal1 @ A )
          = ( k1_ordinal1 @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_ordinal1])).

thf('18',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('19',plain,(
    ! [X62: $i] :
      ( r2_hidden @ X62 @ ( k1_ordinal1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('20',plain,(
    r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( r2_hidden @ X63 @ X64 )
      | ~ ( r1_tarski @ X64 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ X0 ) @ sk_B )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('29',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('30',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ X0 ) @ sk_B )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('34',plain,(
    r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('35',plain,(
    ! [X51: $i,X53: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X51 ) @ X53 )
      | ~ ( r2_hidden @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('36',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X17: $i,X19: $i] :
      ( ( X17 = X19 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( X17 != X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('42',plain,(
    ! [X41: $i] :
      ( ( k2_tarski @ X41 @ X41 )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,(
    ! [X61: $i] :
      ( ( k1_ordinal1 @ X61 )
      = ( k2_xboole_0 @ X61 @ ( k1_tarski @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('45',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_ordinal1 @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k2_tarski @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X41: $i] :
      ( ( k2_tarski @ X41 @ X41 )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_ordinal1 @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,
    ( ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['38','50'])).

thf('52',plain,(
    ! [X62: $i] :
      ( r2_hidden @ X62 @ ( k1_ordinal1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('53',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('56',plain,(
    ! [X36: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X39 @ X38 )
      | ( X39 = X36 )
      | ( X38
       != ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('57',plain,(
    ! [X36: $i,X39: $i] :
      ( ( X39 = X36 )
      | ~ ( r2_hidden @ X39 @ ( k1_tarski @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X51: $i,X53: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X51 ) @ X53 )
      | ~ ( r2_hidden @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('62',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','62'])).

thf('64',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('65',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('67',plain,(
    ! [X57: $i,X58: $i] :
      ( ( ( k4_xboole_0 @ X57 @ ( k1_tarski @ X58 ) )
        = X57 )
      | ( r2_hidden @ X58 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('68',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('71',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ X0 @ X0 ) )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','80'])).

thf('82',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('83',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('94',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','96'])).

thf('98',plain,(
    r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('99',plain,(
    ! [X51: $i,X53: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X51 ) @ X53 )
      | ~ ( r2_hidden @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('100',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('102',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k2_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('103',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_enumset1 @ X42 @ X42 @ X43 )
      = ( k2_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('104',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_tarski @ X35 @ X34 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_enumset1 @ X42 @ X42 @ X43 )
      = ( k2_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('107',plain,(
    ! [X41: $i] :
      ( ( k2_tarski @ X41 @ X41 )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['102','105','108'])).

thf('110',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['97','109'])).

thf('111',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('113',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['110','113'])).

thf('115',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ ( k1_tarski @ X51 ) @ X52 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('116',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['66','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JxJ7qiQd50
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.30/1.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.30/1.51  % Solved by: fo/fo7.sh
% 1.30/1.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.30/1.51  % done 2609 iterations in 1.069s
% 1.30/1.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.30/1.51  % SZS output start Refutation
% 1.30/1.51  thf(sk_A_type, type, sk_A: $i).
% 1.30/1.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.30/1.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.30/1.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.30/1.51  thf(sk_B_type, type, sk_B: $i).
% 1.30/1.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.30/1.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.30/1.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.30/1.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.30/1.51  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 1.30/1.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.30/1.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.30/1.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.30/1.51  thf(d1_ordinal1, axiom,
% 1.30/1.51    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 1.30/1.51  thf('0', plain,
% 1.30/1.51      (![X61 : $i]:
% 1.30/1.51         ((k1_ordinal1 @ X61) = (k2_xboole_0 @ X61 @ (k1_tarski @ X61)))),
% 1.30/1.51      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.30/1.51  thf(commutativity_k2_tarski, axiom,
% 1.30/1.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.30/1.51  thf('1', plain,
% 1.30/1.51      (![X34 : $i, X35 : $i]:
% 1.30/1.51         ((k2_tarski @ X35 @ X34) = (k2_tarski @ X34 @ X35))),
% 1.30/1.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.30/1.51  thf(l51_zfmisc_1, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.30/1.51  thf('2', plain,
% 1.30/1.51      (![X54 : $i, X55 : $i]:
% 1.30/1.51         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 1.30/1.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.30/1.51  thf('3', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.30/1.51      inference('sup+', [status(thm)], ['1', '2'])).
% 1.30/1.51  thf('4', plain,
% 1.30/1.51      (![X54 : $i, X55 : $i]:
% 1.30/1.51         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 1.30/1.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.30/1.51  thf('5', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.30/1.51      inference('sup+', [status(thm)], ['3', '4'])).
% 1.30/1.51  thf(t7_xboole_1, axiom,
% 1.30/1.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.30/1.51  thf('6', plain,
% 1.30/1.51      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 1.30/1.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.30/1.51  thf(t28_xboole_1, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.30/1.51  thf('7', plain,
% 1.30/1.51      (![X20 : $i, X21 : $i]:
% 1.30/1.51         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 1.30/1.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.30/1.51  thf('8', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 1.30/1.51      inference('sup-', [status(thm)], ['6', '7'])).
% 1.30/1.51  thf('9', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 1.30/1.51      inference('sup+', [status(thm)], ['5', '8'])).
% 1.30/1.51  thf('10', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0))
% 1.30/1.51           = (k1_tarski @ X0))),
% 1.30/1.51      inference('sup+', [status(thm)], ['0', '9'])).
% 1.30/1.51  thf('11', plain,
% 1.30/1.51      (![X34 : $i, X35 : $i]:
% 1.30/1.51         ((k2_tarski @ X35 @ X34) = (k2_tarski @ X34 @ X35))),
% 1.30/1.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.30/1.51  thf(t12_setfam_1, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.30/1.51  thf('12', plain,
% 1.30/1.51      (![X59 : $i, X60 : $i]:
% 1.30/1.51         ((k1_setfam_1 @ (k2_tarski @ X59 @ X60)) = (k3_xboole_0 @ X59 @ X60))),
% 1.30/1.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.30/1.51  thf('13', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.30/1.51      inference('sup+', [status(thm)], ['11', '12'])).
% 1.30/1.51  thf('14', plain,
% 1.30/1.51      (![X59 : $i, X60 : $i]:
% 1.30/1.51         ((k1_setfam_1 @ (k2_tarski @ X59 @ X60)) = (k3_xboole_0 @ X59 @ X60))),
% 1.30/1.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.30/1.51  thf('15', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.30/1.51      inference('sup+', [status(thm)], ['13', '14'])).
% 1.30/1.51  thf('16', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((k3_xboole_0 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X0))
% 1.30/1.51           = (k1_tarski @ X0))),
% 1.30/1.51      inference('demod', [status(thm)], ['10', '15'])).
% 1.30/1.51  thf(t48_xboole_1, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.30/1.51  thf('17', plain,
% 1.30/1.51      (![X25 : $i, X26 : $i]:
% 1.30/1.51         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 1.30/1.51           = (k3_xboole_0 @ X25 @ X26))),
% 1.30/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.30/1.51  thf(t12_ordinal1, conjecture,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ))).
% 1.30/1.51  thf(zf_stmt_0, negated_conjecture,
% 1.30/1.51    (~( ![A:$i,B:$i]:
% 1.30/1.51        ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ) )),
% 1.30/1.51    inference('cnf.neg', [status(esa)], [t12_ordinal1])).
% 1.30/1.51  thf('18', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 1.30/1.51  thf('19', plain, (![X62 : $i]: (r2_hidden @ X62 @ (k1_ordinal1 @ X62))),
% 1.30/1.51      inference('cnf', [status(esa)], [t10_ordinal1])).
% 1.30/1.51  thf('20', plain, ((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))),
% 1.30/1.51      inference('sup+', [status(thm)], ['18', '19'])).
% 1.30/1.51  thf(d5_xboole_0, axiom,
% 1.30/1.51    (![A:$i,B:$i,C:$i]:
% 1.30/1.51     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.30/1.51       ( ![D:$i]:
% 1.30/1.51         ( ( r2_hidden @ D @ C ) <=>
% 1.30/1.51           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.30/1.51  thf('21', plain,
% 1.30/1.51      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.30/1.51         (~ (r2_hidden @ X2 @ X3)
% 1.30/1.51          | (r2_hidden @ X2 @ X4)
% 1.30/1.51          | (r2_hidden @ X2 @ X5)
% 1.30/1.51          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.30/1.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.30/1.51  thf('22', plain,
% 1.30/1.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.30/1.51         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 1.30/1.51          | (r2_hidden @ X2 @ X4)
% 1.30/1.51          | ~ (r2_hidden @ X2 @ X3))),
% 1.30/1.51      inference('simplify', [status(thm)], ['21'])).
% 1.30/1.51  thf('23', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((r2_hidden @ sk_B @ X0)
% 1.30/1.51          | (r2_hidden @ sk_B @ (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['20', '22'])).
% 1.30/1.51  thf(t7_ordinal1, axiom,
% 1.30/1.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.30/1.51  thf('24', plain,
% 1.30/1.51      (![X63 : $i, X64 : $i]:
% 1.30/1.51         (~ (r2_hidden @ X63 @ X64) | ~ (r1_tarski @ X64 @ X63))),
% 1.30/1.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.30/1.51  thf('25', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((r2_hidden @ sk_B @ X0)
% 1.30/1.51          | ~ (r1_tarski @ (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ X0) @ sk_B))),
% 1.30/1.51      inference('sup-', [status(thm)], ['23', '24'])).
% 1.30/1.51  thf('26', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (r1_tarski @ (k3_xboole_0 @ (k1_ordinal1 @ sk_A) @ X0) @ sk_B)
% 1.30/1.51          | (r2_hidden @ sk_B @ (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['17', '25'])).
% 1.30/1.51  thf('27', plain,
% 1.30/1.51      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B)
% 1.30/1.51        | (r2_hidden @ sk_B @ 
% 1.30/1.51           (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ (k1_tarski @ sk_A))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['16', '26'])).
% 1.30/1.51  thf('28', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.30/1.51      inference('sup+', [status(thm)], ['13', '14'])).
% 1.30/1.51  thf(t51_xboole_1, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.30/1.51       ( A ) ))).
% 1.30/1.51  thf('29', plain,
% 1.30/1.51      (![X27 : $i, X28 : $i]:
% 1.30/1.51         ((k2_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ (k4_xboole_0 @ X27 @ X28))
% 1.30/1.51           = (X27))),
% 1.30/1.51      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.30/1.51  thf('30', plain,
% 1.30/1.51      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 1.30/1.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.30/1.51  thf('31', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.30/1.51      inference('sup+', [status(thm)], ['29', '30'])).
% 1.30/1.51  thf('32', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.30/1.51      inference('sup+', [status(thm)], ['28', '31'])).
% 1.30/1.51  thf('33', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (r1_tarski @ (k3_xboole_0 @ (k1_ordinal1 @ sk_A) @ X0) @ sk_B)
% 1.30/1.51          | (r2_hidden @ sk_B @ (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['17', '25'])).
% 1.30/1.51  thf('34', plain,
% 1.30/1.51      ((r2_hidden @ sk_B @ (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 1.30/1.51      inference('sup-', [status(thm)], ['32', '33'])).
% 1.30/1.51  thf(l1_zfmisc_1, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.30/1.51  thf('35', plain,
% 1.30/1.51      (![X51 : $i, X53 : $i]:
% 1.30/1.51         ((r1_tarski @ (k1_tarski @ X51) @ X53) | ~ (r2_hidden @ X51 @ X53))),
% 1.30/1.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.30/1.51  thf('36', plain,
% 1.30/1.51      ((r1_tarski @ (k1_tarski @ sk_B) @ 
% 1.30/1.51        (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 1.30/1.51      inference('sup-', [status(thm)], ['34', '35'])).
% 1.30/1.51  thf(d10_xboole_0, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.30/1.51  thf('37', plain,
% 1.30/1.51      (![X17 : $i, X19 : $i]:
% 1.30/1.51         (((X17) = (X19))
% 1.30/1.51          | ~ (r1_tarski @ X19 @ X17)
% 1.30/1.51          | ~ (r1_tarski @ X17 @ X19))),
% 1.30/1.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.30/1.51  thf('38', plain,
% 1.30/1.51      ((~ (r1_tarski @ (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ sk_B) @ 
% 1.30/1.51           (k1_tarski @ sk_B))
% 1.30/1.51        | ((k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ sk_B) = (k1_tarski @ sk_B)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['36', '37'])).
% 1.30/1.51  thf('39', plain,
% 1.30/1.51      (![X17 : $i, X18 : $i]: ((r1_tarski @ X17 @ X18) | ((X17) != (X18)))),
% 1.30/1.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.30/1.51  thf('40', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 1.30/1.51      inference('simplify', [status(thm)], ['39'])).
% 1.30/1.51  thf('41', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf(t69_enumset1, axiom,
% 1.30/1.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.30/1.51  thf('42', plain,
% 1.30/1.51      (![X41 : $i]: ((k2_tarski @ X41 @ X41) = (k1_tarski @ X41))),
% 1.30/1.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.30/1.51  thf('43', plain,
% 1.30/1.51      (![X61 : $i]:
% 1.30/1.51         ((k1_ordinal1 @ X61) = (k2_xboole_0 @ X61 @ (k1_tarski @ X61)))),
% 1.30/1.51      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.30/1.51  thf('44', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 1.30/1.51      inference('sup+', [status(thm)], ['42', '43'])).
% 1.30/1.51  thf(t43_xboole_1, axiom,
% 1.30/1.51    (![A:$i,B:$i,C:$i]:
% 1.30/1.51     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.30/1.51       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.30/1.51  thf('45', plain,
% 1.30/1.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.30/1.51         ((r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 1.30/1.51          | ~ (r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 1.30/1.51      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.30/1.51  thf('46', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         (~ (r1_tarski @ X1 @ (k1_ordinal1 @ X0))
% 1.30/1.51          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k2_tarski @ X0 @ X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['44', '45'])).
% 1.30/1.51  thf('47', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (r1_tarski @ X0 @ (k1_ordinal1 @ sk_A))
% 1.30/1.51          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ (k2_tarski @ sk_B @ sk_B)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['41', '46'])).
% 1.30/1.51  thf('48', plain,
% 1.30/1.51      (![X41 : $i]: ((k2_tarski @ X41 @ X41) = (k1_tarski @ X41))),
% 1.30/1.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.30/1.51  thf('49', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (r1_tarski @ X0 @ (k1_ordinal1 @ sk_A))
% 1.30/1.51          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ (k1_tarski @ sk_B)))),
% 1.30/1.51      inference('demod', [status(thm)], ['47', '48'])).
% 1.30/1.51  thf('50', plain,
% 1.30/1.51      ((r1_tarski @ (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ sk_B) @ 
% 1.30/1.51        (k1_tarski @ sk_B))),
% 1.30/1.51      inference('sup-', [status(thm)], ['40', '49'])).
% 1.30/1.51  thf('51', plain,
% 1.30/1.51      (((k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))),
% 1.30/1.51      inference('demod', [status(thm)], ['38', '50'])).
% 1.30/1.51  thf('52', plain, (![X62 : $i]: (r2_hidden @ X62 @ (k1_ordinal1 @ X62))),
% 1.30/1.51      inference('cnf', [status(esa)], [t10_ordinal1])).
% 1.30/1.51  thf('53', plain,
% 1.30/1.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.30/1.51         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 1.30/1.51          | (r2_hidden @ X2 @ X4)
% 1.30/1.51          | ~ (r2_hidden @ X2 @ X3))),
% 1.30/1.51      inference('simplify', [status(thm)], ['21'])).
% 1.30/1.51  thf('54', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((r2_hidden @ X0 @ X1)
% 1.30/1.51          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_ordinal1 @ X0) @ X1)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['52', '53'])).
% 1.30/1.51  thf('55', plain,
% 1.30/1.51      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B))),
% 1.30/1.51      inference('sup+', [status(thm)], ['51', '54'])).
% 1.30/1.51  thf(d1_tarski, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.30/1.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.30/1.51  thf('56', plain,
% 1.30/1.51      (![X36 : $i, X38 : $i, X39 : $i]:
% 1.30/1.51         (~ (r2_hidden @ X39 @ X38)
% 1.30/1.51          | ((X39) = (X36))
% 1.30/1.51          | ((X38) != (k1_tarski @ X36)))),
% 1.30/1.51      inference('cnf', [status(esa)], [d1_tarski])).
% 1.30/1.51  thf('57', plain,
% 1.30/1.51      (![X36 : $i, X39 : $i]:
% 1.30/1.51         (((X39) = (X36)) | ~ (r2_hidden @ X39 @ (k1_tarski @ X36)))),
% 1.30/1.51      inference('simplify', [status(thm)], ['56'])).
% 1.30/1.51  thf('58', plain, (((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['55', '57'])).
% 1.30/1.51  thf('59', plain, (((sk_A) != (sk_B))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('60', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.30/1.51      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 1.30/1.51  thf('61', plain,
% 1.30/1.51      (![X51 : $i, X53 : $i]:
% 1.30/1.51         ((r1_tarski @ (k1_tarski @ X51) @ X53) | ~ (r2_hidden @ X51 @ X53))),
% 1.30/1.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.30/1.51  thf('62', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 1.30/1.51      inference('sup-', [status(thm)], ['60', '61'])).
% 1.30/1.51  thf('63', plain,
% 1.30/1.51      ((r2_hidden @ sk_B @ 
% 1.30/1.51        (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ (k1_tarski @ sk_A)))),
% 1.30/1.51      inference('demod', [status(thm)], ['27', '62'])).
% 1.30/1.51  thf('64', plain,
% 1.30/1.51      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.30/1.51         (~ (r2_hidden @ X6 @ X5)
% 1.30/1.51          | ~ (r2_hidden @ X6 @ X4)
% 1.30/1.51          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.30/1.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.30/1.51  thf('65', plain,
% 1.30/1.51      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.30/1.51         (~ (r2_hidden @ X6 @ X4)
% 1.30/1.51          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.30/1.51      inference('simplify', [status(thm)], ['64'])).
% 1.30/1.51  thf('66', plain, (~ (r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 1.30/1.51      inference('sup-', [status(thm)], ['63', '65'])).
% 1.30/1.51  thf(t65_zfmisc_1, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.30/1.51       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.30/1.51  thf('67', plain,
% 1.30/1.51      (![X57 : $i, X58 : $i]:
% 1.30/1.51         (((k4_xboole_0 @ X57 @ (k1_tarski @ X58)) = (X57))
% 1.30/1.51          | (r2_hidden @ X58 @ X57))),
% 1.30/1.51      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.30/1.51  thf('68', plain,
% 1.30/1.51      (![X25 : $i, X26 : $i]:
% 1.30/1.51         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 1.30/1.51           = (k3_xboole_0 @ X25 @ X26))),
% 1.30/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.30/1.51  thf('69', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 1.30/1.51          | (r2_hidden @ X1 @ X0))),
% 1.30/1.51      inference('sup+', [status(thm)], ['67', '68'])).
% 1.30/1.51  thf('70', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.30/1.51      inference('sup+', [status(thm)], ['13', '14'])).
% 1.30/1.51  thf('71', plain,
% 1.30/1.51      (![X25 : $i, X26 : $i]:
% 1.30/1.51         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 1.30/1.51           = (k3_xboole_0 @ X25 @ X26))),
% 1.30/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.30/1.51  thf('72', plain,
% 1.30/1.51      (![X25 : $i, X26 : $i]:
% 1.30/1.51         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 1.30/1.51           = (k3_xboole_0 @ X25 @ X26))),
% 1.30/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.30/1.51  thf('73', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.30/1.51           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.30/1.51      inference('sup+', [status(thm)], ['71', '72'])).
% 1.30/1.51  thf('74', plain,
% 1.30/1.51      (![X27 : $i, X28 : $i]:
% 1.30/1.51         ((k2_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ (k4_xboole_0 @ X27 @ X28))
% 1.30/1.51           = (X27))),
% 1.30/1.51      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.30/1.51  thf('75', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 1.30/1.51      inference('sup+', [status(thm)], ['5', '8'])).
% 1.30/1.51  thf('76', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.30/1.51           = (k4_xboole_0 @ X0 @ X1))),
% 1.30/1.51      inference('sup+', [status(thm)], ['74', '75'])).
% 1.30/1.51  thf('77', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.30/1.51      inference('sup+', [status(thm)], ['13', '14'])).
% 1.30/1.51  thf('78', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.30/1.51           = (k4_xboole_0 @ X0 @ X1))),
% 1.30/1.51      inference('demod', [status(thm)], ['76', '77'])).
% 1.30/1.51  thf('79', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.30/1.51           = (k4_xboole_0 @ X1 @ X0))),
% 1.30/1.51      inference('sup+', [status(thm)], ['73', '78'])).
% 1.30/1.51  thf('80', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.30/1.51           = (k4_xboole_0 @ X0 @ X1))),
% 1.30/1.51      inference('sup+', [status(thm)], ['70', '79'])).
% 1.30/1.51  thf('81', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         (((k4_xboole_0 @ (k1_tarski @ X1) @ (k4_xboole_0 @ X0 @ X0))
% 1.30/1.51            = (k4_xboole_0 @ (k1_tarski @ X1) @ X0))
% 1.30/1.51          | (r2_hidden @ X1 @ X0))),
% 1.30/1.51      inference('sup+', [status(thm)], ['69', '80'])).
% 1.30/1.51  thf('82', plain,
% 1.30/1.51      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 1.30/1.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.30/1.51  thf('83', plain,
% 1.30/1.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.30/1.51         ((r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 1.30/1.51          | ~ (r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 1.30/1.51      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.30/1.51  thf('84', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 1.30/1.51      inference('sup-', [status(thm)], ['82', '83'])).
% 1.30/1.51  thf('85', plain,
% 1.30/1.51      (![X20 : $i, X21 : $i]:
% 1.30/1.51         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 1.30/1.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.30/1.51  thf('86', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 1.30/1.51           = (k4_xboole_0 @ X1 @ X1))),
% 1.30/1.51      inference('sup-', [status(thm)], ['84', '85'])).
% 1.30/1.51  thf('87', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.30/1.51      inference('sup+', [status(thm)], ['13', '14'])).
% 1.30/1.51  thf('88', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 1.30/1.51           = (k4_xboole_0 @ X0 @ X0))),
% 1.30/1.51      inference('sup+', [status(thm)], ['86', '87'])).
% 1.30/1.51  thf('89', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 1.30/1.51           = (k4_xboole_0 @ X1 @ X1))),
% 1.30/1.51      inference('sup-', [status(thm)], ['84', '85'])).
% 1.30/1.51  thf('90', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))),
% 1.30/1.51      inference('sup+', [status(thm)], ['88', '89'])).
% 1.30/1.51  thf('91', plain,
% 1.30/1.51      (![X25 : $i, X26 : $i]:
% 1.30/1.51         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 1.30/1.51           = (k3_xboole_0 @ X25 @ X26))),
% 1.30/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.30/1.51  thf('92', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 1.30/1.51           = (k3_xboole_0 @ X1 @ X1))),
% 1.30/1.51      inference('sup+', [status(thm)], ['90', '91'])).
% 1.30/1.51  thf('93', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 1.30/1.51      inference('simplify', [status(thm)], ['39'])).
% 1.30/1.51  thf('94', plain,
% 1.30/1.51      (![X20 : $i, X21 : $i]:
% 1.30/1.51         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 1.30/1.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.30/1.51  thf('95', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['93', '94'])).
% 1.30/1.51  thf('96', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 1.30/1.51      inference('demod', [status(thm)], ['92', '95'])).
% 1.30/1.51  thf('97', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         (((k1_tarski @ X1) = (k4_xboole_0 @ (k1_tarski @ X1) @ X0))
% 1.30/1.51          | (r2_hidden @ X1 @ X0))),
% 1.30/1.51      inference('demod', [status(thm)], ['81', '96'])).
% 1.30/1.51  thf('98', plain, ((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))),
% 1.30/1.51      inference('sup+', [status(thm)], ['18', '19'])).
% 1.30/1.51  thf('99', plain,
% 1.30/1.51      (![X51 : $i, X53 : $i]:
% 1.30/1.51         ((r1_tarski @ (k1_tarski @ X51) @ X53) | ~ (r2_hidden @ X51 @ X53))),
% 1.30/1.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.30/1.51  thf('100', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_ordinal1 @ sk_A))),
% 1.30/1.51      inference('sup-', [status(thm)], ['98', '99'])).
% 1.30/1.51  thf('101', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         (~ (r1_tarski @ X1 @ (k1_ordinal1 @ X0))
% 1.30/1.51          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k2_tarski @ X0 @ X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['44', '45'])).
% 1.30/1.51  thf('102', plain,
% 1.30/1.51      ((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 1.30/1.51        (k2_tarski @ sk_A @ sk_A))),
% 1.30/1.51      inference('sup-', [status(thm)], ['100', '101'])).
% 1.30/1.51  thf(t70_enumset1, axiom,
% 1.30/1.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.30/1.51  thf('103', plain,
% 1.30/1.51      (![X42 : $i, X43 : $i]:
% 1.30/1.51         ((k1_enumset1 @ X42 @ X42 @ X43) = (k2_tarski @ X42 @ X43))),
% 1.30/1.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.30/1.51  thf('104', plain,
% 1.30/1.51      (![X34 : $i, X35 : $i]:
% 1.30/1.51         ((k2_tarski @ X35 @ X34) = (k2_tarski @ X34 @ X35))),
% 1.30/1.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.30/1.51  thf('105', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 1.30/1.51      inference('sup+', [status(thm)], ['103', '104'])).
% 1.30/1.51  thf('106', plain,
% 1.30/1.51      (![X42 : $i, X43 : $i]:
% 1.30/1.51         ((k1_enumset1 @ X42 @ X42 @ X43) = (k2_tarski @ X42 @ X43))),
% 1.30/1.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.30/1.51  thf('107', plain,
% 1.30/1.51      (![X41 : $i]: ((k2_tarski @ X41 @ X41) = (k1_tarski @ X41))),
% 1.30/1.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.30/1.51  thf('108', plain,
% 1.30/1.51      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.30/1.51      inference('sup+', [status(thm)], ['106', '107'])).
% 1.30/1.51  thf('109', plain,
% 1.30/1.51      ((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 1.30/1.51        (k1_tarski @ sk_A))),
% 1.30/1.51      inference('demod', [status(thm)], ['102', '105', '108'])).
% 1.30/1.51  thf('110', plain,
% 1.30/1.51      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 1.30/1.51        | (r2_hidden @ sk_B @ sk_A))),
% 1.30/1.51      inference('sup+', [status(thm)], ['97', '109'])).
% 1.30/1.51  thf('111', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.30/1.51      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 1.30/1.51  thf(antisymmetry_r2_hidden, axiom,
% 1.30/1.51    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 1.30/1.51  thf('112', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 1.30/1.51      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 1.30/1.51  thf('113', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 1.30/1.51      inference('sup-', [status(thm)], ['111', '112'])).
% 1.30/1.51  thf('114', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))),
% 1.30/1.51      inference('clc', [status(thm)], ['110', '113'])).
% 1.30/1.51  thf('115', plain,
% 1.30/1.51      (![X51 : $i, X52 : $i]:
% 1.30/1.51         ((r2_hidden @ X51 @ X52) | ~ (r1_tarski @ (k1_tarski @ X51) @ X52))),
% 1.30/1.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.30/1.51  thf('116', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 1.30/1.51      inference('sup-', [status(thm)], ['114', '115'])).
% 1.30/1.51  thf('117', plain, ($false), inference('demod', [status(thm)], ['66', '116'])).
% 1.30/1.51  
% 1.30/1.51  % SZS output end Refutation
% 1.30/1.51  
% 1.30/1.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
