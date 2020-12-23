%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wvriiZlwbF

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:15 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 137 expanded)
%              Number of leaves         :   25 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  712 (1341 expanded)
%              Number of equality atoms :   66 ( 114 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t32_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( k7_subset_1 @ A @ B @ C )
              = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_subset_1])).

thf('0',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k6_subset_1 @ X23 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ( k6_subset_1 @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k6_subset_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k6_subset_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('13',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k9_subset_1 @ X28 @ X26 @ X27 )
        = ( k3_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k3_xboole_0 @ X0 @ sk_C ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['16'])).

thf('23',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['16'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_C
      = ( k3_xboole_0 @ sk_A @ sk_C ) )
    | ( sk_C
      = ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,
    ( ( sk_C
      = ( k3_xboole_0 @ sk_C @ sk_A ) )
    | ( sk_C
      = ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k6_subset_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['16'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k3_xboole_0 @ X0 @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('47',plain,
    ( ( sk_B
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,
    ( ( sk_B
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X11 @ X13 ) @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( k6_subset_1 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['40','58'])).

thf('60',plain,(
    ( k6_subset_1 @ sk_B @ sk_C )
 != ( k6_subset_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['6','15','59'])).

thf('61',plain,(
    $false ),
    inference(simplify,[status(thm)],['60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wvriiZlwbF
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 21:03:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.04/1.23  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.04/1.23  % Solved by: fo/fo7.sh
% 1.04/1.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.04/1.23  % done 808 iterations in 0.770s
% 1.04/1.23  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.04/1.23  % SZS output start Refutation
% 1.04/1.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.04/1.23  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.04/1.23  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.04/1.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.04/1.23  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.04/1.23  thf(sk_B_type, type, sk_B: $i).
% 1.04/1.23  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.04/1.23  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.04/1.23  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.04/1.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.04/1.23  thf(sk_A_type, type, sk_A: $i).
% 1.04/1.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.04/1.23  thf(sk_C_type, type, sk_C: $i).
% 1.04/1.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.04/1.23  thf(t32_subset_1, conjecture,
% 1.04/1.23    (![A:$i,B:$i]:
% 1.04/1.23     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.04/1.23       ( ![C:$i]:
% 1.04/1.23         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.04/1.23           ( ( k7_subset_1 @ A @ B @ C ) =
% 1.04/1.23             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 1.04/1.23  thf(zf_stmt_0, negated_conjecture,
% 1.04/1.23    (~( ![A:$i,B:$i]:
% 1.04/1.23        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.04/1.23          ( ![C:$i]:
% 1.04/1.23            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.04/1.23              ( ( k7_subset_1 @ A @ B @ C ) =
% 1.04/1.23                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 1.04/1.23    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 1.04/1.23  thf('0', plain,
% 1.04/1.23      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 1.04/1.23         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 1.04/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.23  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.04/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.23  thf(redefinition_k7_subset_1, axiom,
% 1.04/1.23    (![A:$i,B:$i,C:$i]:
% 1.04/1.23     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.04/1.23       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.04/1.23  thf('2', plain,
% 1.04/1.23      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.04/1.23         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 1.04/1.23          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 1.04/1.23      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.04/1.23  thf(redefinition_k6_subset_1, axiom,
% 1.04/1.23    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.04/1.23  thf('3', plain,
% 1.04/1.23      (![X21 : $i, X22 : $i]:
% 1.04/1.23         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 1.04/1.23      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.04/1.23  thf('4', plain,
% 1.04/1.23      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.04/1.23         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 1.04/1.23          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k6_subset_1 @ X23 @ X25)))),
% 1.04/1.23      inference('demod', [status(thm)], ['2', '3'])).
% 1.04/1.23  thf('5', plain,
% 1.04/1.23      (![X0 : $i]:
% 1.04/1.23         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k6_subset_1 @ sk_B @ X0))),
% 1.04/1.23      inference('sup-', [status(thm)], ['1', '4'])).
% 1.04/1.23  thf('6', plain,
% 1.04/1.23      (((k6_subset_1 @ sk_B @ sk_C)
% 1.04/1.23         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 1.04/1.23      inference('demod', [status(thm)], ['0', '5'])).
% 1.04/1.23  thf('7', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.04/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.23  thf(d5_subset_1, axiom,
% 1.04/1.23    (![A:$i,B:$i]:
% 1.04/1.23     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.04/1.23       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.04/1.23  thf('8', plain,
% 1.04/1.23      (![X14 : $i, X15 : $i]:
% 1.04/1.23         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 1.04/1.23          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 1.04/1.23      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.04/1.23  thf('9', plain,
% 1.04/1.23      (![X21 : $i, X22 : $i]:
% 1.04/1.23         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 1.04/1.23      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.04/1.23  thf('10', plain,
% 1.04/1.23      (![X14 : $i, X15 : $i]:
% 1.04/1.23         (((k3_subset_1 @ X14 @ X15) = (k6_subset_1 @ X14 @ X15))
% 1.04/1.23          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 1.04/1.23      inference('demod', [status(thm)], ['8', '9'])).
% 1.04/1.23  thf('11', plain,
% 1.04/1.23      (((k3_subset_1 @ sk_A @ sk_C) = (k6_subset_1 @ sk_A @ sk_C))),
% 1.04/1.23      inference('sup-', [status(thm)], ['7', '10'])).
% 1.04/1.23  thf(dt_k6_subset_1, axiom,
% 1.04/1.23    (![A:$i,B:$i]:
% 1.04/1.23     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.04/1.23  thf('12', plain,
% 1.04/1.23      (![X16 : $i, X17 : $i]:
% 1.04/1.23         (m1_subset_1 @ (k6_subset_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))),
% 1.04/1.23      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.04/1.23  thf('13', plain,
% 1.04/1.23      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 1.04/1.23      inference('sup+', [status(thm)], ['11', '12'])).
% 1.04/1.23  thf(redefinition_k9_subset_1, axiom,
% 1.04/1.23    (![A:$i,B:$i,C:$i]:
% 1.04/1.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.04/1.23       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.04/1.23  thf('14', plain,
% 1.04/1.23      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.04/1.23         (((k9_subset_1 @ X28 @ X26 @ X27) = (k3_xboole_0 @ X26 @ X27))
% 1.04/1.23          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 1.04/1.23      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.04/1.23  thf('15', plain,
% 1.04/1.23      (![X0 : $i]:
% 1.04/1.23         ((k9_subset_1 @ sk_A @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 1.04/1.23           = (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C)))),
% 1.04/1.23      inference('sup-', [status(thm)], ['13', '14'])).
% 1.04/1.23  thf(d4_xboole_0, axiom,
% 1.04/1.23    (![A:$i,B:$i,C:$i]:
% 1.04/1.23     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.04/1.23       ( ![D:$i]:
% 1.04/1.23         ( ( r2_hidden @ D @ C ) <=>
% 1.04/1.23           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.04/1.23  thf('16', plain,
% 1.04/1.23      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.04/1.23         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.04/1.23          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.04/1.23          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.04/1.23      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.04/1.23  thf('17', plain,
% 1.04/1.23      (![X0 : $i, X1 : $i]:
% 1.04/1.23         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.04/1.23          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.04/1.23      inference('eq_fact', [status(thm)], ['16'])).
% 1.04/1.23  thf('18', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.04/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.23  thf(l3_subset_1, axiom,
% 1.04/1.23    (![A:$i,B:$i]:
% 1.04/1.23     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.04/1.23       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.04/1.23  thf('19', plain,
% 1.04/1.23      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.04/1.23         (~ (r2_hidden @ X18 @ X19)
% 1.04/1.23          | (r2_hidden @ X18 @ X20)
% 1.04/1.23          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.04/1.23      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.04/1.23  thf('20', plain,
% 1.04/1.23      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C))),
% 1.04/1.23      inference('sup-', [status(thm)], ['18', '19'])).
% 1.04/1.23  thf('21', plain,
% 1.04/1.23      (![X0 : $i]:
% 1.04/1.23         (((sk_C) = (k3_xboole_0 @ X0 @ sk_C))
% 1.04/1.23          | (r2_hidden @ (sk_D @ sk_C @ sk_C @ X0) @ sk_A))),
% 1.04/1.23      inference('sup-', [status(thm)], ['17', '20'])).
% 1.04/1.23  thf('22', plain,
% 1.04/1.23      (![X0 : $i, X1 : $i]:
% 1.04/1.23         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.04/1.23          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.04/1.23      inference('eq_fact', [status(thm)], ['16'])).
% 1.04/1.23  thf('23', plain,
% 1.04/1.23      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.04/1.23         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.04/1.23          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.04/1.23          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.04/1.23          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.04/1.23      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.04/1.23  thf('24', plain,
% 1.04/1.23      (![X0 : $i, X1 : $i]:
% 1.04/1.23         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.04/1.23          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.04/1.23          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.04/1.23          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.04/1.23      inference('sup-', [status(thm)], ['22', '23'])).
% 1.04/1.23  thf('25', plain,
% 1.04/1.23      (![X0 : $i, X1 : $i]:
% 1.04/1.23         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.04/1.23          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.04/1.23          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.04/1.23      inference('simplify', [status(thm)], ['24'])).
% 1.04/1.23  thf('26', plain,
% 1.04/1.23      (![X0 : $i, X1 : $i]:
% 1.04/1.23         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.04/1.23          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.04/1.23      inference('eq_fact', [status(thm)], ['16'])).
% 1.04/1.23  thf('27', plain,
% 1.04/1.23      (![X0 : $i, X1 : $i]:
% 1.04/1.23         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.04/1.23          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.04/1.23      inference('clc', [status(thm)], ['25', '26'])).
% 1.04/1.24  thf('28', plain,
% 1.04/1.24      ((((sk_C) = (k3_xboole_0 @ sk_A @ sk_C))
% 1.04/1.24        | ((sk_C) = (k3_xboole_0 @ sk_A @ sk_C)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['21', '27'])).
% 1.04/1.24  thf(commutativity_k3_xboole_0, axiom,
% 1.04/1.24    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.04/1.24  thf('29', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.04/1.24  thf('30', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.04/1.24  thf('31', plain,
% 1.04/1.24      ((((sk_C) = (k3_xboole_0 @ sk_C @ sk_A))
% 1.04/1.24        | ((sk_C) = (k3_xboole_0 @ sk_C @ sk_A)))),
% 1.04/1.24      inference('demod', [status(thm)], ['28', '29', '30'])).
% 1.04/1.24  thf('32', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ sk_A))),
% 1.04/1.24      inference('simplify', [status(thm)], ['31'])).
% 1.04/1.24  thf('33', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.04/1.24  thf(t100_xboole_1, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.04/1.24  thf('34', plain,
% 1.04/1.24      (![X9 : $i, X10 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ X9 @ X10)
% 1.04/1.24           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 1.04/1.24      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.04/1.24  thf('35', plain,
% 1.04/1.24      (![X21 : $i, X22 : $i]:
% 1.04/1.24         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 1.04/1.24      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.04/1.24  thf('36', plain,
% 1.04/1.24      (![X9 : $i, X10 : $i]:
% 1.04/1.24         ((k6_subset_1 @ X9 @ X10)
% 1.04/1.24           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 1.04/1.24      inference('demod', [status(thm)], ['34', '35'])).
% 1.04/1.24  thf('37', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         ((k6_subset_1 @ X0 @ X1)
% 1.04/1.24           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.04/1.24      inference('sup+', [status(thm)], ['33', '36'])).
% 1.04/1.24  thf('38', plain,
% 1.04/1.24      (((k6_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 1.04/1.24      inference('sup+', [status(thm)], ['32', '37'])).
% 1.04/1.24  thf('39', plain,
% 1.04/1.24      (((k3_subset_1 @ sk_A @ sk_C) = (k6_subset_1 @ sk_A @ sk_C))),
% 1.04/1.24      inference('sup-', [status(thm)], ['7', '10'])).
% 1.04/1.24  thf('40', plain,
% 1.04/1.24      (((k3_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 1.04/1.24      inference('demod', [status(thm)], ['38', '39'])).
% 1.04/1.24  thf('41', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.04/1.24          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.04/1.24      inference('eq_fact', [status(thm)], ['16'])).
% 1.04/1.24  thf('42', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('43', plain,
% 1.04/1.24      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.04/1.24         (~ (r2_hidden @ X18 @ X19)
% 1.04/1.24          | (r2_hidden @ X18 @ X20)
% 1.04/1.24          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.04/1.24      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.04/1.24  thf('44', plain,
% 1.04/1.24      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 1.04/1.24      inference('sup-', [status(thm)], ['42', '43'])).
% 1.04/1.24  thf('45', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         (((sk_B) = (k3_xboole_0 @ X0 @ sk_B))
% 1.04/1.24          | (r2_hidden @ (sk_D @ sk_B @ sk_B @ X0) @ sk_A))),
% 1.04/1.24      inference('sup-', [status(thm)], ['41', '44'])).
% 1.04/1.24  thf('46', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.04/1.24          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.04/1.24      inference('clc', [status(thm)], ['25', '26'])).
% 1.04/1.24  thf('47', plain,
% 1.04/1.24      ((((sk_B) = (k3_xboole_0 @ sk_A @ sk_B))
% 1.04/1.24        | ((sk_B) = (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['45', '46'])).
% 1.04/1.24  thf('48', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.04/1.24  thf('49', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.04/1.24  thf('50', plain,
% 1.04/1.24      ((((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))
% 1.04/1.24        | ((sk_B) = (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.04/1.24      inference('demod', [status(thm)], ['47', '48', '49'])).
% 1.04/1.24  thf('51', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.04/1.24      inference('simplify', [status(thm)], ['50'])).
% 1.04/1.24  thf('52', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.04/1.24  thf(t112_xboole_1, axiom,
% 1.04/1.24    (![A:$i,B:$i,C:$i]:
% 1.04/1.24     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 1.04/1.24       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.04/1.24  thf('53', plain,
% 1.04/1.24      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.04/1.24         ((k5_xboole_0 @ (k3_xboole_0 @ X11 @ X13) @ (k3_xboole_0 @ X12 @ X13))
% 1.04/1.24           = (k3_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13))),
% 1.04/1.24      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.04/1.24  thf('54', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.24         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 1.04/1.24           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 1.04/1.24      inference('sup+', [status(thm)], ['52', '53'])).
% 1.04/1.24  thf('55', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 1.04/1.24           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.04/1.24      inference('sup+', [status(thm)], ['51', '54'])).
% 1.04/1.24  thf('56', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         ((k6_subset_1 @ X0 @ X1)
% 1.04/1.24           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.04/1.24      inference('sup+', [status(thm)], ['33', '36'])).
% 1.04/1.24  thf('57', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.04/1.24  thf('58', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         ((k6_subset_1 @ sk_B @ X0)
% 1.04/1.24           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 1.04/1.24      inference('demod', [status(thm)], ['55', '56', '57'])).
% 1.04/1.24  thf('59', plain,
% 1.04/1.24      (((k6_subset_1 @ sk_B @ sk_C)
% 1.04/1.24         = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 1.04/1.24      inference('sup+', [status(thm)], ['40', '58'])).
% 1.04/1.24  thf('60', plain,
% 1.04/1.24      (((k6_subset_1 @ sk_B @ sk_C) != (k6_subset_1 @ sk_B @ sk_C))),
% 1.04/1.24      inference('demod', [status(thm)], ['6', '15', '59'])).
% 1.04/1.24  thf('61', plain, ($false), inference('simplify', [status(thm)], ['60'])).
% 1.04/1.24  
% 1.04/1.24  % SZS output end Refutation
% 1.04/1.24  
% 1.04/1.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
