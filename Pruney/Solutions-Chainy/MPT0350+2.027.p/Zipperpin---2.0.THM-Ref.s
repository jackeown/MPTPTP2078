%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.koMtzRCj7j

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:48 EST 2020

% Result     : Theorem 8.52s
% Output     : Refutation 8.52s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 154 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  740 (1229 expanded)
%              Number of equality atoms :   66 ( 104 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ( X17
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ( r2_hidden @ ( sk_D_1 @ X17 @ X14 @ X13 ) @ X13 )
      | ( r2_hidden @ ( sk_D_1 @ X17 @ X14 @ X13 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X26: $i] :
      ( ( k2_xboole_0 @ X26 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k4_xboole_0 @ X54 @ ( k2_xboole_0 @ X54 @ X55 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( r2_hidden @ X22 @ X20 )
      | ( X21
       != ( k4_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('5',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k4_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X43: $i] :
      ( ( k2_xboole_0 @ X43 @ k1_xboole_0 )
      = X43 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('12',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k2_xboole_0 @ X44 @ ( k3_xboole_0 @ X44 @ X45 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X94: $i,X95: $i,X96: $i] :
      ( ~ ( m1_subset_1 @ X94 @ ( k1_zfmisc_1 @ X95 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X95 @ X94 @ X96 ) @ ( k1_zfmisc_1 @ X95 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X103: $i,X104: $i,X105: $i] :
      ( ~ ( m1_subset_1 @ X103 @ ( k1_zfmisc_1 @ X104 ) )
      | ( ( k7_subset_1 @ X104 @ X103 @ X105 )
        = ( k4_xboole_0 @ X103 @ X105 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X90: $i,X91: $i] :
      ( ( ( k3_subset_1 @ X90 @ X91 )
        = ( k4_xboole_0 @ X90 @ X91 ) )
      | ~ ( m1_subset_1 @ X91 @ ( k1_zfmisc_1 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k2_xboole_0 @ X44 @ ( k3_xboole_0 @ X44 @ X45 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k4_xboole_0 @ X54 @ ( k2_xboole_0 @ X54 @ X55 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('29',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( k3_xboole_0 @ X58 @ ( k4_xboole_0 @ X59 @ X60 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X58 @ X59 ) @ X60 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k4_xboole_0 @ X31 @ X32 )
      = ( k5_xboole_0 @ X31 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('33',plain,(
    ! [X73: $i] :
      ( ( k5_xboole_0 @ X73 @ k1_xboole_0 )
      = X73 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) )
    = sk_A ),
    inference('sup+',[status(thm)],['23','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('37',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k4_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('41',plain,(
    ! [X97: $i,X98: $i,X99: $i] :
      ( ~ ( r2_hidden @ X97 @ X98 )
      | ( r2_hidden @ X97 @ X99 )
      | ~ ( m1_subset_1 @ X98 @ ( k1_zfmisc_1 @ X99 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k7_subset_1 @ sk_A @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['39','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','45'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k2_xboole_0 @ X46 @ ( k4_xboole_0 @ X47 @ X46 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('48',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('52',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('54',plain,(
    ! [X89: $i] :
      ( ( k2_subset_1 @ X89 )
      = X89 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('55',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
 != sk_A ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('57',plain,(
    ! [X92: $i,X93: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X92 @ X93 ) @ ( k1_zfmisc_1 @ X92 ) )
      | ~ ( m1_subset_1 @ X93 @ ( k1_zfmisc_1 @ X92 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('58',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('60',plain,(
    ! [X100: $i,X101: $i,X102: $i] :
      ( ~ ( m1_subset_1 @ X100 @ ( k1_zfmisc_1 @ X101 ) )
      | ~ ( m1_subset_1 @ X102 @ ( k1_zfmisc_1 @ X101 ) )
      | ( ( k4_subset_1 @ X101 @ X100 @ X102 )
        = ( k2_xboole_0 @ X100 @ X102 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X90: $i,X91: $i] :
      ( ( ( k3_subset_1 @ X90 @ X91 )
        = ( k4_xboole_0 @ X90 @ X91 ) )
      | ~ ( m1_subset_1 @ X91 @ ( k1_zfmisc_1 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('65',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k2_xboole_0 @ X46 @ ( k4_xboole_0 @ X47 @ X46 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('67',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('69',plain,(
    ( k2_xboole_0 @ sk_B_1 @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['55','68'])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.koMtzRCj7j
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:19:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 8.52/8.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.52/8.71  % Solved by: fo/fo7.sh
% 8.52/8.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.52/8.71  % done 5416 iterations in 8.249s
% 8.52/8.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.52/8.71  % SZS output start Refutation
% 8.52/8.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.52/8.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 8.52/8.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.52/8.71  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 8.52/8.71  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 8.52/8.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.52/8.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.52/8.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 8.52/8.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.52/8.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.52/8.71  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 8.52/8.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.52/8.71  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 8.52/8.71  thf(sk_A_type, type, sk_A: $i).
% 8.52/8.71  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 8.52/8.71  thf(d4_xboole_0, axiom,
% 8.52/8.71    (![A:$i,B:$i,C:$i]:
% 8.52/8.71     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 8.52/8.71       ( ![D:$i]:
% 8.52/8.71         ( ( r2_hidden @ D @ C ) <=>
% 8.52/8.71           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 8.52/8.71  thf('0', plain,
% 8.52/8.71      (![X13 : $i, X14 : $i, X17 : $i]:
% 8.52/8.71         (((X17) = (k3_xboole_0 @ X13 @ X14))
% 8.52/8.71          | (r2_hidden @ (sk_D_1 @ X17 @ X14 @ X13) @ X13)
% 8.52/8.71          | (r2_hidden @ (sk_D_1 @ X17 @ X14 @ X13) @ X17))),
% 8.52/8.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 8.52/8.71  thf(idempotence_k2_xboole_0, axiom,
% 8.52/8.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 8.52/8.71  thf('1', plain, (![X26 : $i]: ((k2_xboole_0 @ X26 @ X26) = (X26))),
% 8.52/8.71      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 8.52/8.71  thf(t46_xboole_1, axiom,
% 8.52/8.71    (![A:$i,B:$i]:
% 8.52/8.71     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 8.52/8.71  thf('2', plain,
% 8.52/8.71      (![X54 : $i, X55 : $i]:
% 8.52/8.71         ((k4_xboole_0 @ X54 @ (k2_xboole_0 @ X54 @ X55)) = (k1_xboole_0))),
% 8.52/8.71      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.52/8.71  thf('3', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 8.52/8.71      inference('sup+', [status(thm)], ['1', '2'])).
% 8.52/8.71  thf(d5_xboole_0, axiom,
% 8.52/8.71    (![A:$i,B:$i,C:$i]:
% 8.52/8.71     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 8.52/8.71       ( ![D:$i]:
% 8.52/8.71         ( ( r2_hidden @ D @ C ) <=>
% 8.52/8.71           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 8.52/8.71  thf('4', plain,
% 8.52/8.71      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 8.52/8.71         (~ (r2_hidden @ X22 @ X21)
% 8.52/8.71          | ~ (r2_hidden @ X22 @ X20)
% 8.52/8.71          | ((X21) != (k4_xboole_0 @ X19 @ X20)))),
% 8.52/8.71      inference('cnf', [status(esa)], [d5_xboole_0])).
% 8.52/8.71  thf('5', plain,
% 8.52/8.71      (![X19 : $i, X20 : $i, X22 : $i]:
% 8.52/8.71         (~ (r2_hidden @ X22 @ X20)
% 8.52/8.71          | ~ (r2_hidden @ X22 @ (k4_xboole_0 @ X19 @ X20)))),
% 8.52/8.71      inference('simplify', [status(thm)], ['4'])).
% 8.52/8.71  thf('6', plain,
% 8.52/8.71      (![X0 : $i, X1 : $i]:
% 8.52/8.71         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 8.52/8.71      inference('sup-', [status(thm)], ['3', '5'])).
% 8.52/8.71  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 8.52/8.71      inference('condensation', [status(thm)], ['6'])).
% 8.52/8.71  thf('8', plain,
% 8.52/8.71      (![X0 : $i, X1 : $i]:
% 8.52/8.71         ((r2_hidden @ (sk_D_1 @ X1 @ X0 @ k1_xboole_0) @ X1)
% 8.52/8.71          | ((X1) = (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 8.52/8.71      inference('sup-', [status(thm)], ['0', '7'])).
% 8.52/8.71  thf(commutativity_k2_xboole_0, axiom,
% 8.52/8.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 8.52/8.71  thf('9', plain,
% 8.52/8.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.52/8.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.52/8.71  thf(t1_boole, axiom,
% 8.52/8.71    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 8.52/8.71  thf('10', plain, (![X43 : $i]: ((k2_xboole_0 @ X43 @ k1_xboole_0) = (X43))),
% 8.52/8.71      inference('cnf', [status(esa)], [t1_boole])).
% 8.52/8.71  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.52/8.71      inference('sup+', [status(thm)], ['9', '10'])).
% 8.52/8.71  thf(t22_xboole_1, axiom,
% 8.52/8.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 8.52/8.71  thf('12', plain,
% 8.52/8.71      (![X44 : $i, X45 : $i]:
% 8.52/8.71         ((k2_xboole_0 @ X44 @ (k3_xboole_0 @ X44 @ X45)) = (X44))),
% 8.52/8.71      inference('cnf', [status(esa)], [t22_xboole_1])).
% 8.52/8.71  thf('13', plain,
% 8.52/8.71      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 8.52/8.71      inference('sup+', [status(thm)], ['11', '12'])).
% 8.52/8.71  thf('14', plain,
% 8.52/8.71      (![X0 : $i, X1 : $i]:
% 8.52/8.71         ((r2_hidden @ (sk_D_1 @ X1 @ X0 @ k1_xboole_0) @ X1)
% 8.52/8.71          | ((X1) = (k1_xboole_0)))),
% 8.52/8.71      inference('demod', [status(thm)], ['8', '13'])).
% 8.52/8.71  thf(t25_subset_1, conjecture,
% 8.52/8.71    (![A:$i,B:$i]:
% 8.52/8.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.52/8.71       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 8.52/8.71         ( k2_subset_1 @ A ) ) ))).
% 8.52/8.71  thf(zf_stmt_0, negated_conjecture,
% 8.52/8.71    (~( ![A:$i,B:$i]:
% 8.52/8.71        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.52/8.71          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 8.52/8.71            ( k2_subset_1 @ A ) ) ) )),
% 8.52/8.71    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 8.52/8.71  thf('15', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 8.52/8.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.52/8.71  thf(dt_k7_subset_1, axiom,
% 8.52/8.71    (![A:$i,B:$i,C:$i]:
% 8.52/8.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.52/8.71       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 8.52/8.71  thf('16', plain,
% 8.52/8.71      (![X94 : $i, X95 : $i, X96 : $i]:
% 8.52/8.71         (~ (m1_subset_1 @ X94 @ (k1_zfmisc_1 @ X95))
% 8.52/8.71          | (m1_subset_1 @ (k7_subset_1 @ X95 @ X94 @ X96) @ 
% 8.52/8.71             (k1_zfmisc_1 @ X95)))),
% 8.52/8.71      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 8.52/8.71  thf('17', plain,
% 8.52/8.71      (![X0 : $i]:
% 8.52/8.71         (m1_subset_1 @ (k7_subset_1 @ sk_A @ sk_B_1 @ X0) @ 
% 8.52/8.71          (k1_zfmisc_1 @ sk_A))),
% 8.52/8.71      inference('sup-', [status(thm)], ['15', '16'])).
% 8.52/8.71  thf('18', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 8.52/8.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.52/8.71  thf(redefinition_k7_subset_1, axiom,
% 8.52/8.71    (![A:$i,B:$i,C:$i]:
% 8.52/8.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.52/8.71       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 8.52/8.71  thf('19', plain,
% 8.52/8.71      (![X103 : $i, X104 : $i, X105 : $i]:
% 8.52/8.71         (~ (m1_subset_1 @ X103 @ (k1_zfmisc_1 @ X104))
% 8.52/8.71          | ((k7_subset_1 @ X104 @ X103 @ X105) = (k4_xboole_0 @ X103 @ X105)))),
% 8.52/8.71      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.52/8.71  thf('20', plain,
% 8.52/8.71      (![X0 : $i]:
% 8.52/8.71         ((k7_subset_1 @ sk_A @ sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 8.52/8.71      inference('sup-', [status(thm)], ['18', '19'])).
% 8.52/8.71  thf('21', plain,
% 8.52/8.71      (![X0 : $i]:
% 8.52/8.71         (m1_subset_1 @ (k4_xboole_0 @ sk_B_1 @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 8.52/8.71      inference('demod', [status(thm)], ['17', '20'])).
% 8.52/8.71  thf(d5_subset_1, axiom,
% 8.52/8.71    (![A:$i,B:$i]:
% 8.52/8.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.52/8.71       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 8.52/8.71  thf('22', plain,
% 8.52/8.71      (![X90 : $i, X91 : $i]:
% 8.52/8.71         (((k3_subset_1 @ X90 @ X91) = (k4_xboole_0 @ X90 @ X91))
% 8.52/8.71          | ~ (m1_subset_1 @ X91 @ (k1_zfmisc_1 @ X90)))),
% 8.52/8.71      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.52/8.71  thf('23', plain,
% 8.52/8.71      (![X0 : $i]:
% 8.52/8.71         ((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ X0))
% 8.52/8.71           = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ X0)))),
% 8.52/8.71      inference('sup-', [status(thm)], ['21', '22'])).
% 8.52/8.71  thf('24', plain,
% 8.52/8.71      (![X44 : $i, X45 : $i]:
% 8.52/8.71         ((k2_xboole_0 @ X44 @ (k3_xboole_0 @ X44 @ X45)) = (X44))),
% 8.52/8.71      inference('cnf', [status(esa)], [t22_xboole_1])).
% 8.52/8.71  thf('25', plain,
% 8.52/8.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.52/8.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.52/8.71  thf('26', plain,
% 8.52/8.71      (![X54 : $i, X55 : $i]:
% 8.52/8.71         ((k4_xboole_0 @ X54 @ (k2_xboole_0 @ X54 @ X55)) = (k1_xboole_0))),
% 8.52/8.71      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.52/8.71  thf('27', plain,
% 8.52/8.71      (![X0 : $i, X1 : $i]:
% 8.52/8.71         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 8.52/8.71      inference('sup+', [status(thm)], ['25', '26'])).
% 8.52/8.71  thf('28', plain,
% 8.52/8.71      (![X0 : $i, X1 : $i]:
% 8.52/8.71         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 8.52/8.71      inference('sup+', [status(thm)], ['24', '27'])).
% 8.52/8.71  thf(t49_xboole_1, axiom,
% 8.52/8.71    (![A:$i,B:$i,C:$i]:
% 8.52/8.71     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 8.52/8.71       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 8.52/8.71  thf('29', plain,
% 8.52/8.71      (![X58 : $i, X59 : $i, X60 : $i]:
% 8.52/8.71         ((k3_xboole_0 @ X58 @ (k4_xboole_0 @ X59 @ X60))
% 8.52/8.71           = (k4_xboole_0 @ (k3_xboole_0 @ X58 @ X59) @ X60))),
% 8.52/8.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 8.52/8.71  thf('30', plain,
% 8.52/8.71      (![X0 : $i, X1 : $i]:
% 8.52/8.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 8.52/8.71      inference('demod', [status(thm)], ['28', '29'])).
% 8.52/8.71  thf(t100_xboole_1, axiom,
% 8.52/8.71    (![A:$i,B:$i]:
% 8.52/8.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 8.52/8.71  thf('31', plain,
% 8.52/8.71      (![X31 : $i, X32 : $i]:
% 8.52/8.71         ((k4_xboole_0 @ X31 @ X32)
% 8.52/8.71           = (k5_xboole_0 @ X31 @ (k3_xboole_0 @ X31 @ X32)))),
% 8.52/8.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 8.52/8.71  thf('32', plain,
% 8.52/8.71      (![X0 : $i, X1 : $i]:
% 8.52/8.71         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 8.52/8.71           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 8.52/8.71      inference('sup+', [status(thm)], ['30', '31'])).
% 8.52/8.71  thf(t5_boole, axiom,
% 8.52/8.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 8.52/8.71  thf('33', plain, (![X73 : $i]: ((k5_xboole_0 @ X73 @ k1_xboole_0) = (X73))),
% 8.52/8.71      inference('cnf', [status(esa)], [t5_boole])).
% 8.52/8.71  thf('34', plain,
% 8.52/8.71      (![X0 : $i, X1 : $i]:
% 8.52/8.71         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 8.52/8.71      inference('demod', [status(thm)], ['32', '33'])).
% 8.52/8.71  thf('35', plain,
% 8.52/8.71      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_A)) = (sk_A))),
% 8.52/8.71      inference('sup+', [status(thm)], ['23', '34'])).
% 8.52/8.71  thf('36', plain,
% 8.52/8.71      (![X0 : $i]:
% 8.52/8.71         ((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ X0))
% 8.52/8.71           = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ X0)))),
% 8.52/8.71      inference('sup-', [status(thm)], ['21', '22'])).
% 8.52/8.71  thf('37', plain,
% 8.52/8.71      (![X19 : $i, X20 : $i, X22 : $i]:
% 8.52/8.71         (~ (r2_hidden @ X22 @ X20)
% 8.52/8.71          | ~ (r2_hidden @ X22 @ (k4_xboole_0 @ X19 @ X20)))),
% 8.52/8.71      inference('simplify', [status(thm)], ['4'])).
% 8.52/8.71  thf('38', plain,
% 8.52/8.71      (![X0 : $i, X1 : $i]:
% 8.52/8.71         (~ (r2_hidden @ X1 @ 
% 8.52/8.71             (k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ X0)))
% 8.52/8.71          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ sk_B_1 @ X0)))),
% 8.52/8.71      inference('sup-', [status(thm)], ['36', '37'])).
% 8.52/8.71  thf('39', plain,
% 8.52/8.71      (![X0 : $i]:
% 8.52/8.71         (~ (r2_hidden @ X0 @ sk_A)
% 8.52/8.71          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B_1 @ sk_A)))),
% 8.52/8.71      inference('sup-', [status(thm)], ['35', '38'])).
% 8.52/8.71  thf('40', plain,
% 8.52/8.71      (![X0 : $i]:
% 8.52/8.71         (m1_subset_1 @ (k7_subset_1 @ sk_A @ sk_B_1 @ X0) @ 
% 8.52/8.71          (k1_zfmisc_1 @ sk_A))),
% 8.52/8.71      inference('sup-', [status(thm)], ['15', '16'])).
% 8.52/8.71  thf(l3_subset_1, axiom,
% 8.52/8.71    (![A:$i,B:$i]:
% 8.52/8.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.52/8.71       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 8.52/8.71  thf('41', plain,
% 8.52/8.71      (![X97 : $i, X98 : $i, X99 : $i]:
% 8.52/8.71         (~ (r2_hidden @ X97 @ X98)
% 8.52/8.71          | (r2_hidden @ X97 @ X99)
% 8.52/8.71          | ~ (m1_subset_1 @ X98 @ (k1_zfmisc_1 @ X99)))),
% 8.52/8.71      inference('cnf', [status(esa)], [l3_subset_1])).
% 8.52/8.71  thf('42', plain,
% 8.52/8.71      (![X0 : $i, X1 : $i]:
% 8.52/8.71         ((r2_hidden @ X1 @ sk_A)
% 8.52/8.71          | ~ (r2_hidden @ X1 @ (k7_subset_1 @ sk_A @ sk_B_1 @ X0)))),
% 8.52/8.71      inference('sup-', [status(thm)], ['40', '41'])).
% 8.52/8.71  thf('43', plain,
% 8.52/8.71      (![X0 : $i]:
% 8.52/8.71         ((k7_subset_1 @ sk_A @ sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 8.52/8.71      inference('sup-', [status(thm)], ['18', '19'])).
% 8.52/8.71  thf('44', plain,
% 8.52/8.71      (![X0 : $i, X1 : $i]:
% 8.52/8.71         ((r2_hidden @ X1 @ sk_A)
% 8.52/8.71          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ sk_B_1 @ X0)))),
% 8.52/8.71      inference('demod', [status(thm)], ['42', '43'])).
% 8.52/8.71  thf('45', plain,
% 8.52/8.71      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 8.52/8.71      inference('clc', [status(thm)], ['39', '44'])).
% 8.52/8.71  thf('46', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 8.52/8.71      inference('sup-', [status(thm)], ['14', '45'])).
% 8.52/8.71  thf(t39_xboole_1, axiom,
% 8.52/8.71    (![A:$i,B:$i]:
% 8.52/8.71     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 8.52/8.71  thf('47', plain,
% 8.52/8.71      (![X46 : $i, X47 : $i]:
% 8.52/8.71         ((k2_xboole_0 @ X46 @ (k4_xboole_0 @ X47 @ X46))
% 8.52/8.71           = (k2_xboole_0 @ X46 @ X47))),
% 8.52/8.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.52/8.71  thf('48', plain,
% 8.52/8.71      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B_1))),
% 8.52/8.71      inference('sup+', [status(thm)], ['46', '47'])).
% 8.52/8.71  thf('49', plain,
% 8.52/8.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.52/8.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.52/8.71  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.52/8.71      inference('sup+', [status(thm)], ['9', '10'])).
% 8.52/8.71  thf('51', plain,
% 8.52/8.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.52/8.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.52/8.71  thf('52', plain, (((sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 8.52/8.71      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 8.52/8.71  thf('53', plain,
% 8.52/8.71      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 8.52/8.71         != (k2_subset_1 @ sk_A))),
% 8.52/8.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.52/8.71  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 8.52/8.71  thf('54', plain, (![X89 : $i]: ((k2_subset_1 @ X89) = (X89))),
% 8.52/8.71      inference('cnf', [status(esa)], [d4_subset_1])).
% 8.52/8.71  thf('55', plain,
% 8.52/8.71      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) != (sk_A))),
% 8.52/8.71      inference('demod', [status(thm)], ['53', '54'])).
% 8.52/8.71  thf('56', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 8.52/8.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.52/8.71  thf(dt_k3_subset_1, axiom,
% 8.52/8.71    (![A:$i,B:$i]:
% 8.52/8.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.52/8.71       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 8.52/8.71  thf('57', plain,
% 8.52/8.71      (![X92 : $i, X93 : $i]:
% 8.52/8.71         ((m1_subset_1 @ (k3_subset_1 @ X92 @ X93) @ (k1_zfmisc_1 @ X92))
% 8.52/8.71          | ~ (m1_subset_1 @ X93 @ (k1_zfmisc_1 @ X92)))),
% 8.52/8.71      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 8.52/8.71  thf('58', plain,
% 8.52/8.71      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 8.52/8.71      inference('sup-', [status(thm)], ['56', '57'])).
% 8.52/8.71  thf('59', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 8.52/8.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.52/8.71  thf(redefinition_k4_subset_1, axiom,
% 8.52/8.71    (![A:$i,B:$i,C:$i]:
% 8.52/8.71     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 8.52/8.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 8.52/8.71       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 8.52/8.71  thf('60', plain,
% 8.52/8.71      (![X100 : $i, X101 : $i, X102 : $i]:
% 8.52/8.71         (~ (m1_subset_1 @ X100 @ (k1_zfmisc_1 @ X101))
% 8.52/8.71          | ~ (m1_subset_1 @ X102 @ (k1_zfmisc_1 @ X101))
% 8.52/8.71          | ((k4_subset_1 @ X101 @ X100 @ X102) = (k2_xboole_0 @ X100 @ X102)))),
% 8.52/8.71      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 8.52/8.71  thf('61', plain,
% 8.52/8.71      (![X0 : $i]:
% 8.52/8.71         (((k4_subset_1 @ sk_A @ sk_B_1 @ X0) = (k2_xboole_0 @ sk_B_1 @ X0))
% 8.52/8.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 8.52/8.71      inference('sup-', [status(thm)], ['59', '60'])).
% 8.52/8.71  thf('62', plain,
% 8.52/8.71      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 8.52/8.71         = (k2_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 8.52/8.71      inference('sup-', [status(thm)], ['58', '61'])).
% 8.52/8.71  thf('63', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 8.52/8.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.52/8.71  thf('64', plain,
% 8.52/8.71      (![X90 : $i, X91 : $i]:
% 8.52/8.71         (((k3_subset_1 @ X90 @ X91) = (k4_xboole_0 @ X90 @ X91))
% 8.52/8.71          | ~ (m1_subset_1 @ X91 @ (k1_zfmisc_1 @ X90)))),
% 8.52/8.71      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.52/8.71  thf('65', plain,
% 8.52/8.71      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 8.52/8.71      inference('sup-', [status(thm)], ['63', '64'])).
% 8.52/8.71  thf('66', plain,
% 8.52/8.71      (![X46 : $i, X47 : $i]:
% 8.52/8.71         ((k2_xboole_0 @ X46 @ (k4_xboole_0 @ X47 @ X46))
% 8.52/8.71           = (k2_xboole_0 @ X46 @ X47))),
% 8.52/8.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.52/8.71  thf('67', plain,
% 8.52/8.71      (((k2_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 8.52/8.71         = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 8.52/8.71      inference('sup+', [status(thm)], ['65', '66'])).
% 8.52/8.71  thf('68', plain,
% 8.52/8.71      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 8.52/8.71         = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 8.52/8.71      inference('demod', [status(thm)], ['62', '67'])).
% 8.52/8.71  thf('69', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) != (sk_A))),
% 8.52/8.71      inference('demod', [status(thm)], ['55', '68'])).
% 8.52/8.71  thf('70', plain, ($false),
% 8.52/8.71      inference('simplify_reflect-', [status(thm)], ['52', '69'])).
% 8.52/8.71  
% 8.52/8.71  % SZS output end Refutation
% 8.52/8.71  
% 8.52/8.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
