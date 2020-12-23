%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KdSJXzM8tb

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:38 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 145 expanded)
%              Number of leaves         :   41 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :  898 (1611 expanded)
%              Number of equality atoms :  103 ( 153 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ( X35 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X36 @ X33 ) @ ( k2_relset_1 @ X34 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','6','7','8'])).

thf('10',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X15
        = ( k1_enumset1 @ X12 @ X13 @ X14 ) )
      | ( X15
        = ( k2_tarski @ X12 @ X14 ) )
      | ( X15
        = ( k2_tarski @ X13 @ X14 ) )
      | ( X15
        = ( k2_tarski @ X12 @ X13 ) )
      | ( X15
        = ( k1_tarski @ X14 ) )
      | ( X15
        = ( k1_tarski @ X13 ) )
      | ( X15
        = ( k1_tarski @ X12 ) )
      | ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X3
        = ( k1_tarski @ X2 ) )
      | ( X3
        = ( k1_tarski @ X1 ) )
      | ( X3
        = ( k1_tarski @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X1 ) )
      | ( X3
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X0 ) )
      | ( X3
        = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_tarski @ sk_A @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','39'])).

thf('41',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != ( k1_tarski @ X20 ) )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_tarski @ ( k1_funct_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('49',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('52',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['49','52'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('54',plain,(
    ! [X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('57',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['57'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('59',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('60',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('61',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('62',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['18','58','59','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KdSJXzM8tb
% 0.15/0.36  % Computer   : n002.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:48:52 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.23/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.23/0.57  % Solved by: fo/fo7.sh
% 0.23/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.57  % done 293 iterations in 0.103s
% 0.23/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.23/0.57  % SZS output start Refutation
% 0.23/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.23/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.23/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.23/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.23/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.23/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.23/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.58  thf(d1_xboole_0, axiom,
% 0.23/0.58    (![A:$i]:
% 0.23/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.58  thf('0', plain,
% 0.23/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.23/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.58  thf(t62_funct_2, conjecture,
% 0.23/0.58    (![A:$i,B:$i,C:$i]:
% 0.23/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.23/0.58         ( m1_subset_1 @
% 0.23/0.58           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.23/0.58       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.23/0.58         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.23/0.58           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.23/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.58        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.23/0.58            ( m1_subset_1 @
% 0.23/0.58              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.23/0.58          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.23/0.58            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.23/0.58              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.23/0.58    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.23/0.58  thf('1', plain,
% 0.23/0.58      ((m1_subset_1 @ sk_C @ 
% 0.23/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.23/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.58  thf(t6_funct_2, axiom,
% 0.23/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.23/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.58       ( ( r2_hidden @ C @ A ) =>
% 0.23/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.23/0.58           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.23/0.58  thf('2', plain,
% 0.23/0.58      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.23/0.58         (~ (r2_hidden @ X33 @ X34)
% 0.23/0.58          | ((X35) = (k1_xboole_0))
% 0.23/0.58          | ~ (v1_funct_1 @ X36)
% 0.23/0.58          | ~ (v1_funct_2 @ X36 @ X34 @ X35)
% 0.23/0.58          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.23/0.58          | (r2_hidden @ (k1_funct_1 @ X36 @ X33) @ 
% 0.23/0.58             (k2_relset_1 @ X34 @ X35 @ X36)))),
% 0.23/0.58      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.23/0.58  thf('3', plain,
% 0.23/0.58      (![X0 : $i]:
% 0.23/0.58         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ 
% 0.23/0.58           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))
% 0.23/0.58          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.23/0.58          | ~ (v1_funct_1 @ sk_C)
% 0.23/0.58          | ((sk_B_1) = (k1_xboole_0))
% 0.23/0.58          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.23/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.58  thf('4', plain,
% 0.23/0.58      ((m1_subset_1 @ sk_C @ 
% 0.23/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.23/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.23/0.58    (![A:$i,B:$i,C:$i]:
% 0.23/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.23/0.58  thf('5', plain,
% 0.23/0.58      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.23/0.58         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 0.23/0.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.23/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.23/0.58  thf('6', plain,
% 0.23/0.58      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.23/0.58         = (k2_relat_1 @ sk_C))),
% 0.23/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.58  thf('7', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.23/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.58  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.23/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.58  thf('9', plain,
% 0.23/0.58      (![X0 : $i]:
% 0.23/0.58         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.23/0.58          | ((sk_B_1) = (k1_xboole_0))
% 0.23/0.58          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.23/0.58      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 0.23/0.58  thf('10', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.23/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.58  thf('11', plain,
% 0.23/0.58      (![X0 : $i]:
% 0.23/0.58         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.23/0.58          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.23/0.58      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.23/0.58  thf('12', plain,
% 0.23/0.58      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.23/0.58        | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.23/0.58           (k2_relat_1 @ sk_C)))),
% 0.23/0.58      inference('sup-', [status(thm)], ['0', '11'])).
% 0.23/0.58  thf(t69_enumset1, axiom,
% 0.23/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.23/0.58  thf('13', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.23/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.58  thf(fc3_xboole_0, axiom,
% 0.23/0.58    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) ))).
% 0.23/0.58  thf('14', plain,
% 0.23/0.58      (![X10 : $i, X11 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X10 @ X11))),
% 0.23/0.58      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 0.23/0.58  thf('15', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.23/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.58  thf('16', plain,
% 0.23/0.58      ((r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.23/0.58        (k2_relat_1 @ sk_C))),
% 0.23/0.58      inference('clc', [status(thm)], ['12', '15'])).
% 0.23/0.58  thf('17', plain,
% 0.23/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.23/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.58  thf('18', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.23/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.58  thf('19', plain,
% 0.23/0.58      ((m1_subset_1 @ sk_C @ 
% 0.23/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.23/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.58  thf(cc2_relset_1, axiom,
% 0.23/0.58    (![A:$i,B:$i,C:$i]:
% 0.23/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.23/0.58  thf('20', plain,
% 0.23/0.58      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.23/0.58         ((v4_relat_1 @ X27 @ X28)
% 0.23/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.23/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.23/0.58  thf('21', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.23/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.58  thf(d18_relat_1, axiom,
% 0.23/0.58    (![A:$i,B:$i]:
% 0.23/0.58     ( ( v1_relat_1 @ B ) =>
% 0.23/0.58       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.23/0.58  thf('22', plain,
% 0.23/0.58      (![X17 : $i, X18 : $i]:
% 0.23/0.58         (~ (v4_relat_1 @ X17 @ X18)
% 0.23/0.58          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.23/0.58          | ~ (v1_relat_1 @ X17))),
% 0.23/0.58      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.23/0.58  thf('23', plain,
% 0.23/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.23/0.58        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 0.23/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.23/0.58  thf('24', plain,
% 0.23/0.58      ((m1_subset_1 @ sk_C @ 
% 0.23/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.23/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.58  thf(cc1_relset_1, axiom,
% 0.23/0.58    (![A:$i,B:$i,C:$i]:
% 0.23/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.58       ( v1_relat_1 @ C ) ))).
% 0.23/0.58  thf('25', plain,
% 0.23/0.58      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.23/0.58         ((v1_relat_1 @ X24)
% 0.23/0.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.23/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.23/0.58  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.23/0.58  thf('27', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.23/0.58      inference('demod', [status(thm)], ['23', '26'])).
% 0.23/0.58  thf(t71_enumset1, axiom,
% 0.23/0.58    (![A:$i,B:$i,C:$i]:
% 0.23/0.58     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.23/0.58  thf('28', plain,
% 0.23/0.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.58         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.23/0.58      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.23/0.58  thf(t70_enumset1, axiom,
% 0.23/0.58    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.23/0.58  thf('29', plain,
% 0.23/0.58      (![X5 : $i, X6 : $i]:
% 0.23/0.58         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.23/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.23/0.58  thf('30', plain,
% 0.23/0.58      (![X0 : $i, X1 : $i]:
% 0.23/0.58         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.23/0.58      inference('sup+', [status(thm)], ['28', '29'])).
% 0.23/0.58  thf('31', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.23/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.58  thf('32', plain,
% 0.23/0.58      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.23/0.58      inference('sup+', [status(thm)], ['30', '31'])).
% 0.23/0.58  thf('33', plain,
% 0.23/0.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.58         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.23/0.58      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.23/0.58  thf(t142_zfmisc_1, axiom,
% 0.23/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.58     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.23/0.58       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.23/0.58            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.23/0.58            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.23/0.58            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.23/0.58            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.23/0.58            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.23/0.58  thf('34', plain,
% 0.23/0.58      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.58         (((X15) = (k1_enumset1 @ X12 @ X13 @ X14))
% 0.23/0.58          | ((X15) = (k2_tarski @ X12 @ X14))
% 0.23/0.58          | ((X15) = (k2_tarski @ X13 @ X14))
% 0.23/0.58          | ((X15) = (k2_tarski @ X12 @ X13))
% 0.23/0.58          | ((X15) = (k1_tarski @ X14))
% 0.23/0.58          | ((X15) = (k1_tarski @ X13))
% 0.23/0.58          | ((X15) = (k1_tarski @ X12))
% 0.23/0.58          | ((X15) = (k1_xboole_0))
% 0.23/0.58          | ~ (r1_tarski @ X15 @ (k1_enumset1 @ X12 @ X13 @ X14)))),
% 0.23/0.58      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.23/0.58  thf('35', plain,
% 0.23/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.58         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 0.23/0.58          | ((X3) = (k1_xboole_0))
% 0.23/0.58          | ((X3) = (k1_tarski @ X2))
% 0.23/0.58          | ((X3) = (k1_tarski @ X1))
% 0.23/0.58          | ((X3) = (k1_tarski @ X0))
% 0.23/0.58          | ((X3) = (k2_tarski @ X2 @ X1))
% 0.23/0.58          | ((X3) = (k2_tarski @ X1 @ X0))
% 0.23/0.58          | ((X3) = (k2_tarski @ X2 @ X0))
% 0.23/0.58          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.23/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.23/0.58  thf('36', plain,
% 0.23/0.58      (![X0 : $i, X1 : $i]:
% 0.23/0.58         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.23/0.58          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 0.23/0.58          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.23/0.58          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.23/0.58          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.23/0.58          | ((X1) = (k1_tarski @ X0))
% 0.23/0.58          | ((X1) = (k1_tarski @ X0))
% 0.23/0.58          | ((X1) = (k1_tarski @ X0))
% 0.23/0.58          | ((X1) = (k1_xboole_0)))),
% 0.23/0.58      inference('sup-', [status(thm)], ['32', '35'])).
% 0.23/0.58  thf('37', plain,
% 0.23/0.58      (![X5 : $i, X6 : $i]:
% 0.23/0.58         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.23/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.23/0.58  thf('38', plain,
% 0.23/0.58      (![X0 : $i, X1 : $i]:
% 0.23/0.58         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.23/0.58          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.23/0.58          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.23/0.58          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.23/0.58          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.23/0.58          | ((X1) = (k1_tarski @ X0))
% 0.23/0.58          | ((X1) = (k1_tarski @ X0))
% 0.23/0.58          | ((X1) = (k1_tarski @ X0))
% 0.23/0.58          | ((X1) = (k1_xboole_0)))),
% 0.23/0.58      inference('demod', [status(thm)], ['36', '37'])).
% 0.23/0.58  thf('39', plain,
% 0.23/0.58      (![X0 : $i, X1 : $i]:
% 0.23/0.58         (((X1) = (k1_xboole_0))
% 0.23/0.58          | ((X1) = (k1_tarski @ X0))
% 0.23/0.58          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.23/0.58          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.23/0.58      inference('simplify', [status(thm)], ['38'])).
% 0.23/0.58  thf('40', plain,
% 0.23/0.58      ((((k1_relat_1 @ sk_C) = (k2_tarski @ sk_A @ sk_A))
% 0.23/0.58        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.23/0.58        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.23/0.58      inference('sup-', [status(thm)], ['27', '39'])).
% 0.23/0.58  thf('41', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.23/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.58  thf('42', plain,
% 0.23/0.58      ((((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.23/0.58        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.23/0.58        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.23/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.23/0.58  thf('43', plain,
% 0.23/0.58      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.23/0.58        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 0.23/0.58      inference('simplify', [status(thm)], ['42'])).
% 0.23/0.58  thf(t14_funct_1, axiom,
% 0.23/0.58    (![A:$i,B:$i]:
% 0.23/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.58       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.23/0.58         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.23/0.58  thf('44', plain,
% 0.23/0.58      (![X20 : $i, X21 : $i]:
% 0.23/0.58         (((k1_relat_1 @ X21) != (k1_tarski @ X20))
% 0.23/0.58          | ((k2_relat_1 @ X21) = (k1_tarski @ (k1_funct_1 @ X21 @ X20)))
% 0.23/0.58          | ~ (v1_funct_1 @ X21)
% 0.23/0.58          | ~ (v1_relat_1 @ X21))),
% 0.23/0.58      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.23/0.58  thf('45', plain,
% 0.23/0.58      (![X0 : $i]:
% 0.23/0.58         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.23/0.58          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.23/0.58          | ~ (v1_relat_1 @ X0)
% 0.23/0.58          | ~ (v1_funct_1 @ X0)
% 0.23/0.58          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.23/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.23/0.58  thf('46', plain,
% 0.23/0.58      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.23/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.23/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.23/0.58        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.23/0.58      inference('eq_res', [status(thm)], ['45'])).
% 0.23/0.58  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 0.23/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.58  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.23/0.58  thf('49', plain,
% 0.23/0.58      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.23/0.58        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.23/0.58      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.23/0.58  thf('50', plain,
% 0.23/0.58      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.23/0.58         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.23/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.58  thf('51', plain,
% 0.23/0.58      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.23/0.58         = (k2_relat_1 @ sk_C))),
% 0.23/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.58  thf('52', plain,
% 0.23/0.58      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.23/0.58      inference('demod', [status(thm)], ['50', '51'])).
% 0.23/0.58  thf('53', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.23/0.58      inference('simplify_reflect-', [status(thm)], ['49', '52'])).
% 0.23/0.58  thf(t64_relat_1, axiom,
% 0.23/0.58    (![A:$i]:
% 0.23/0.58     ( ( v1_relat_1 @ A ) =>
% 0.23/0.58       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.23/0.58           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.23/0.58         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.58  thf('54', plain,
% 0.23/0.58      (![X19 : $i]:
% 0.23/0.58         (((k1_relat_1 @ X19) != (k1_xboole_0))
% 0.23/0.58          | ((X19) = (k1_xboole_0))
% 0.23/0.58          | ~ (v1_relat_1 @ X19))),
% 0.23/0.58      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.23/0.58  thf('55', plain,
% 0.23/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.23/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.23/0.58        | ((sk_C) = (k1_xboole_0)))),
% 0.23/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.23/0.58  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.23/0.58  thf('57', plain,
% 0.23/0.58      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.23/0.58      inference('demod', [status(thm)], ['55', '56'])).
% 0.23/0.58  thf('58', plain, (((sk_C) = (k1_xboole_0))),
% 0.23/0.58      inference('simplify', [status(thm)], ['57'])).
% 0.23/0.58  thf(t60_relat_1, axiom,
% 0.23/0.58    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.23/0.58     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.23/0.58  thf('59', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.23/0.58  thf('60', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.23/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.23/0.58  thf('61', plain,
% 0.23/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.23/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.58  thf(t7_ordinal1, axiom,
% 0.23/0.58    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.58  thf('62', plain,
% 0.23/0.58      (![X22 : $i, X23 : $i]:
% 0.23/0.58         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 0.23/0.58      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.23/0.58  thf('63', plain,
% 0.23/0.58      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.23/0.58      inference('sup-', [status(thm)], ['61', '62'])).
% 0.23/0.58  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.58      inference('sup-', [status(thm)], ['60', '63'])).
% 0.23/0.58  thf('65', plain, ($false),
% 0.23/0.58      inference('demod', [status(thm)], ['18', '58', '59', '64'])).
% 0.23/0.58  
% 0.23/0.58  % SZS output end Refutation
% 0.23/0.58  
% 0.42/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
