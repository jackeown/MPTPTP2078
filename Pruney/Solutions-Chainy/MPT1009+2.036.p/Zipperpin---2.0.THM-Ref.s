%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3f2MWvR7EG

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:53 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 384 expanded)
%              Number of leaves         :   40 ( 132 expanded)
%              Depth                    :   17
%              Number of atoms          :  860 (5005 expanded)
%              Number of equality atoms :   97 ( 433 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k7_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k9_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X38 ) @ X39 )
      | ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) @ sk_D )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X23 @ X24 ) @ ( k2_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v4_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X16
        = ( k1_enumset1 @ X13 @ X14 @ X15 ) )
      | ( X16
        = ( k2_tarski @ X13 @ X15 ) )
      | ( X16
        = ( k2_tarski @ X14 @ X15 ) )
      | ( X16
        = ( k2_tarski @ X13 @ X14 ) )
      | ( X16
        = ( k1_tarski @ X15 ) )
      | ( X16
        = ( k1_tarski @ X14 ) )
      | ( X16
        = ( k1_tarski @ X13 ) )
      | ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('32',plain,(
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
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
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
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('35',plain,(
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
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','36'])).

thf('38',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != ( k1_tarski @ X26 ) )
      | ( ( k2_relat_1 @ X27 )
        = ( k1_tarski @ ( k1_funct_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['42'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('48',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('53',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('54',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('56',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('57',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['14','51','53','54','55','56'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('58',plain,(
    ! [X25: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('59',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['14','51','53','54','55','56'])).

thf('60',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['4','57','58','59','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3f2MWvR7EG
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:53:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.60/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.84  % Solved by: fo/fo7.sh
% 0.60/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.84  % done 1015 iterations in 0.385s
% 0.60/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.84  % SZS output start Refutation
% 0.60/0.84  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.60/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.84  thf(sk_D_type, type, sk_D: $i).
% 0.60/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.84  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.60/0.84  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.60/0.84  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.84  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.60/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.84  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.60/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.84  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.60/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.84  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.60/0.84  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.60/0.84  thf(t64_funct_2, conjecture,
% 0.60/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.84     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.60/0.84         ( m1_subset_1 @
% 0.60/0.84           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.60/0.84       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.60/0.84         ( r1_tarski @
% 0.60/0.84           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.60/0.84           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.60/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.84    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.84        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.60/0.84            ( m1_subset_1 @
% 0.60/0.84              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.60/0.84          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.60/0.84            ( r1_tarski @
% 0.60/0.84              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.60/0.84              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.60/0.84    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.60/0.84  thf('0', plain,
% 0.60/0.84      (~ (r1_tarski @ 
% 0.60/0.84          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.60/0.84          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('1', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ 
% 0.60/0.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(redefinition_k7_relset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.84       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.60/0.84  thf('2', plain,
% 0.60/0.84      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.60/0.84          | ((k7_relset_1 @ X35 @ X36 @ X34 @ X37) = (k9_relat_1 @ X34 @ X37)))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.60/0.84  thf('3', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.60/0.84           = (k9_relat_1 @ sk_D @ X0))),
% 0.60/0.84      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.84  thf('4', plain,
% 0.60/0.84      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.60/0.84          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.60/0.84      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.84  thf(d10_xboole_0, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.84  thf('5', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.60/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.84  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.60/0.84      inference('simplify', [status(thm)], ['5'])).
% 0.60/0.84  thf('7', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ 
% 0.60/0.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(t13_relset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.60/0.84       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.60/0.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.60/0.84  thf('8', plain,
% 0.60/0.84      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.60/0.84         (~ (r1_tarski @ (k1_relat_1 @ X38) @ X39)
% 0.60/0.84          | (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.60/0.84          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.60/0.84      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.60/0.84  thf('9', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.60/0.84          | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 0.60/0.84      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.84  thf('10', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ 
% 0.60/0.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['6', '9'])).
% 0.60/0.84  thf(t3_subset, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.60/0.84  thf('11', plain,
% 0.60/0.84      (![X18 : $i, X19 : $i]:
% 0.60/0.84         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.60/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.60/0.84  thf('12', plain,
% 0.60/0.84      ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.60/0.84      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.84  thf('13', plain,
% 0.60/0.84      (![X0 : $i, X2 : $i]:
% 0.60/0.84         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.60/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.84  thf('14', plain,
% 0.60/0.84      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B) @ sk_D)
% 0.60/0.84        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B) = (sk_D)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['12', '13'])).
% 0.60/0.84  thf(t144_relat_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ B ) =>
% 0.60/0.84       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.60/0.84  thf('15', plain,
% 0.60/0.84      (![X23 : $i, X24 : $i]:
% 0.60/0.84         ((r1_tarski @ (k9_relat_1 @ X23 @ X24) @ (k2_relat_1 @ X23))
% 0.60/0.84          | ~ (v1_relat_1 @ X23))),
% 0.60/0.84      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.60/0.84  thf('16', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ 
% 0.60/0.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(cc2_relset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.84       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.60/0.84  thf('17', plain,
% 0.60/0.84      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.60/0.84         ((v4_relat_1 @ X31 @ X32)
% 0.60/0.84          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.60/0.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.60/0.84  thf('18', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.60/0.84      inference('sup-', [status(thm)], ['16', '17'])).
% 0.60/0.84  thf(d18_relat_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ B ) =>
% 0.60/0.84       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.60/0.84  thf('19', plain,
% 0.60/0.84      (![X21 : $i, X22 : $i]:
% 0.60/0.84         (~ (v4_relat_1 @ X21 @ X22)
% 0.60/0.84          | (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 0.60/0.84          | ~ (v1_relat_1 @ X21))),
% 0.60/0.84      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.60/0.84  thf('20', plain,
% 0.60/0.84      ((~ (v1_relat_1 @ sk_D)
% 0.60/0.84        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['18', '19'])).
% 0.60/0.84  thf('21', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ 
% 0.60/0.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(cc1_relset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.84       ( v1_relat_1 @ C ) ))).
% 0.60/0.84  thf('22', plain,
% 0.60/0.84      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.60/0.84         ((v1_relat_1 @ X28)
% 0.60/0.84          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.60/0.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.60/0.84  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.84      inference('sup-', [status(thm)], ['21', '22'])).
% 0.60/0.84  thf('24', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.60/0.84      inference('demod', [status(thm)], ['20', '23'])).
% 0.60/0.84  thf(t71_enumset1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.60/0.84  thf('25', plain,
% 0.60/0.84      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.60/0.84         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.60/0.84      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.60/0.84  thf(t70_enumset1, axiom,
% 0.60/0.84    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.60/0.84  thf('26', plain,
% 0.60/0.84      (![X5 : $i, X6 : $i]:
% 0.60/0.84         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.60/0.84      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.60/0.84  thf('27', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.60/0.84      inference('sup+', [status(thm)], ['25', '26'])).
% 0.60/0.84  thf(t69_enumset1, axiom,
% 0.60/0.84    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.60/0.84  thf('28', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.60/0.84      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.84  thf('29', plain,
% 0.60/0.84      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.60/0.84      inference('sup+', [status(thm)], ['27', '28'])).
% 0.60/0.84  thf('30', plain,
% 0.60/0.84      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.60/0.84         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.60/0.84      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.60/0.84  thf(t142_zfmisc_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.84     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.60/0.84       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.60/0.84            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.60/0.84            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.60/0.84            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.60/0.84            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.60/0.84            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.60/0.84  thf('31', plain,
% 0.60/0.84      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.60/0.84         (((X16) = (k1_enumset1 @ X13 @ X14 @ X15))
% 0.60/0.84          | ((X16) = (k2_tarski @ X13 @ X15))
% 0.60/0.84          | ((X16) = (k2_tarski @ X14 @ X15))
% 0.60/0.84          | ((X16) = (k2_tarski @ X13 @ X14))
% 0.60/0.84          | ((X16) = (k1_tarski @ X15))
% 0.60/0.84          | ((X16) = (k1_tarski @ X14))
% 0.60/0.84          | ((X16) = (k1_tarski @ X13))
% 0.60/0.84          | ((X16) = (k1_xboole_0))
% 0.60/0.84          | ~ (r1_tarski @ X16 @ (k1_enumset1 @ X13 @ X14 @ X15)))),
% 0.60/0.84      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.60/0.84  thf('32', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.84         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 0.60/0.84          | ((X3) = (k1_xboole_0))
% 0.60/0.84          | ((X3) = (k1_tarski @ X2))
% 0.60/0.84          | ((X3) = (k1_tarski @ X1))
% 0.60/0.84          | ((X3) = (k1_tarski @ X0))
% 0.60/0.84          | ((X3) = (k2_tarski @ X2 @ X1))
% 0.60/0.84          | ((X3) = (k2_tarski @ X1 @ X0))
% 0.60/0.84          | ((X3) = (k2_tarski @ X2 @ X0))
% 0.60/0.84          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['30', '31'])).
% 0.60/0.84  thf('33', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.60/0.84          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 0.60/0.84          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.60/0.84          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.60/0.84          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.60/0.84          | ((X1) = (k1_tarski @ X0))
% 0.60/0.84          | ((X1) = (k1_tarski @ X0))
% 0.60/0.84          | ((X1) = (k1_tarski @ X0))
% 0.60/0.84          | ((X1) = (k1_xboole_0)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['29', '32'])).
% 0.60/0.84  thf('34', plain,
% 0.60/0.84      (![X5 : $i, X6 : $i]:
% 0.60/0.84         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.60/0.84      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.60/0.84  thf('35', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.60/0.84          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.60/0.84          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.60/0.84          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.60/0.84          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.60/0.84          | ((X1) = (k1_tarski @ X0))
% 0.60/0.84          | ((X1) = (k1_tarski @ X0))
% 0.60/0.84          | ((X1) = (k1_tarski @ X0))
% 0.60/0.84          | ((X1) = (k1_xboole_0)))),
% 0.60/0.84      inference('demod', [status(thm)], ['33', '34'])).
% 0.60/0.84  thf('36', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (((X1) = (k1_xboole_0))
% 0.60/0.84          | ((X1) = (k1_tarski @ X0))
% 0.60/0.84          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.60/0.84          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.60/0.84      inference('simplify', [status(thm)], ['35'])).
% 0.60/0.84  thf('37', plain,
% 0.60/0.84      ((((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A))
% 0.60/0.84        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.60/0.84        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['24', '36'])).
% 0.60/0.84  thf('38', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.60/0.84      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.84  thf('39', plain,
% 0.60/0.84      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.60/0.84        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.60/0.84        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.60/0.84      inference('demod', [status(thm)], ['37', '38'])).
% 0.60/0.84  thf('40', plain,
% 0.60/0.84      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.60/0.84        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.60/0.84      inference('simplify', [status(thm)], ['39'])).
% 0.60/0.84  thf(t14_funct_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.84       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.60/0.84         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.60/0.84  thf('41', plain,
% 0.60/0.84      (![X26 : $i, X27 : $i]:
% 0.60/0.84         (((k1_relat_1 @ X27) != (k1_tarski @ X26))
% 0.60/0.84          | ((k2_relat_1 @ X27) = (k1_tarski @ (k1_funct_1 @ X27 @ X26)))
% 0.60/0.84          | ~ (v1_funct_1 @ X27)
% 0.60/0.84          | ~ (v1_relat_1 @ X27))),
% 0.60/0.84      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.60/0.84  thf('42', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.60/0.84          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.60/0.84          | ~ (v1_relat_1 @ X0)
% 0.60/0.84          | ~ (v1_funct_1 @ X0)
% 0.60/0.84          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.60/0.84      inference('sup-', [status(thm)], ['40', '41'])).
% 0.60/0.84  thf('43', plain,
% 0.60/0.84      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.60/0.84        | ~ (v1_funct_1 @ sk_D)
% 0.60/0.84        | ~ (v1_relat_1 @ sk_D)
% 0.60/0.84        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.60/0.84      inference('eq_res', [status(thm)], ['42'])).
% 0.60/0.84  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('45', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.84      inference('sup-', [status(thm)], ['21', '22'])).
% 0.60/0.84  thf('46', plain,
% 0.60/0.84      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.60/0.84        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.60/0.84      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.60/0.84  thf('47', plain,
% 0.60/0.84      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.60/0.84          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.60/0.84      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.84  thf('48', plain,
% 0.60/0.84      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.60/0.84        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['46', '47'])).
% 0.60/0.84  thf('49', plain,
% 0.60/0.84      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['15', '48'])).
% 0.60/0.84  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.84      inference('sup-', [status(thm)], ['21', '22'])).
% 0.60/0.84  thf('51', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.60/0.84      inference('demod', [status(thm)], ['49', '50'])).
% 0.60/0.84  thf(t113_zfmisc_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.60/0.84       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.60/0.84  thf('52', plain,
% 0.60/0.84      (![X11 : $i, X12 : $i]:
% 0.60/0.84         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.60/0.84          | ((X11) != (k1_xboole_0)))),
% 0.60/0.84      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.60/0.84  thf('53', plain,
% 0.60/0.84      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.60/0.84      inference('simplify', [status(thm)], ['52'])).
% 0.60/0.84  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.60/0.84  thf('54', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.60/0.84      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.60/0.84  thf('55', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.60/0.84      inference('demod', [status(thm)], ['49', '50'])).
% 0.60/0.84  thf('56', plain,
% 0.60/0.84      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.60/0.84      inference('simplify', [status(thm)], ['52'])).
% 0.60/0.84  thf('57', plain, (((k1_xboole_0) = (sk_D))),
% 0.60/0.84      inference('demod', [status(thm)], ['14', '51', '53', '54', '55', '56'])).
% 0.60/0.84  thf(t150_relat_1, axiom,
% 0.60/0.84    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.60/0.84  thf('58', plain,
% 0.60/0.84      (![X25 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X25) = (k1_xboole_0))),
% 0.60/0.84      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.60/0.84  thf('59', plain, (((k1_xboole_0) = (sk_D))),
% 0.60/0.84      inference('demod', [status(thm)], ['14', '51', '53', '54', '55', '56'])).
% 0.60/0.84  thf('60', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.60/0.84      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.60/0.84  thf('61', plain, ($false),
% 0.60/0.84      inference('demod', [status(thm)], ['4', '57', '58', '59', '60'])).
% 0.60/0.84  
% 0.60/0.84  % SZS output end Refutation
% 0.60/0.84  
% 0.60/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
