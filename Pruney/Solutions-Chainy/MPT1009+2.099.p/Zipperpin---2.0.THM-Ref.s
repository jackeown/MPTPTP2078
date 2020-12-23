%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NVzLNhbi8A

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:02 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 135 expanded)
%              Number of leaves         :   42 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  846 (1489 expanded)
%              Number of equality atoms :   98 ( 123 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k7_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k9_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X15 @ X16 ) @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X27 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('8',plain,(
    m1_subset_1 @ ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
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

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X10
        = ( k1_enumset1 @ X7 @ X8 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X7 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X8 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X7 @ X8 ) )
      | ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10
        = ( k1_tarski @ X8 ) )
      | ( X10
        = ( k1_tarski @ X7 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('22',plain,(
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
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
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
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('25',plain,(
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
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('28',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != ( k1_tarski @ X22 ) )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_tarski @ ( k1_funct_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['32'])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','37'])).

thf('39',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['35','36'])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('44',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 )
      | ( ( k9_relat_1 @ X18 @ X19 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k9_relat_1 @ sk_D @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('46',plain,(
    ! [X17: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('47',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k9_relat_1 @ X18 @ X19 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('49',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('52',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['35','36'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_D @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','54','55'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['4','56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NVzLNhbi8A
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 478 iterations in 0.140s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.60  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.41/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.60  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.41/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.60  thf(t64_funct_2, conjecture,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.41/0.60         ( m1_subset_1 @
% 0.41/0.60           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.41/0.60       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.41/0.60         ( r1_tarski @
% 0.41/0.60           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.41/0.60           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.41/0.60            ( m1_subset_1 @
% 0.41/0.60              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.41/0.60          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.41/0.60            ( r1_tarski @
% 0.41/0.60              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.41/0.60              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      (~ (r1_tarski @ 
% 0.41/0.60          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.41/0.60          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(redefinition_k7_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.41/0.60          | ((k7_relset_1 @ X34 @ X35 @ X33 @ X36) = (k9_relat_1 @ X33 @ X36)))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.41/0.60           = (k9_relat_1 @ sk_D @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.41/0.60          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.41/0.60  thf(t144_relat_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( v1_relat_1 @ B ) =>
% 0.41/0.60       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X15 : $i, X16 : $i]:
% 0.41/0.60         ((r1_tarski @ (k9_relat_1 @ X15 @ X16) @ (k2_relat_1 @ X15))
% 0.41/0.60          | ~ (v1_relat_1 @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(dt_k1_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.41/0.60         ((m1_subset_1 @ (k1_relset_1 @ X27 @ X28 @ X29) @ (k1_zfmisc_1 @ X27))
% 0.41/0.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      ((m1_subset_1 @ (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.41/0.60         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.41/0.60          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.41/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      ((m1_subset_1 @ (k1_relat_1 @ sk_D) @ (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['8', '11'])).
% 0.41/0.60  thf(t3_subset, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X12 : $i, X13 : $i]:
% 0.41/0.60         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.60  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.60  thf(t71_enumset1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.60         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.41/0.60      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.41/0.60  thf(t70_enumset1, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i]:
% 0.41/0.60         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.41/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['15', '16'])).
% 0.41/0.60  thf(t69_enumset1, axiom,
% 0.41/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.60  thf('18', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['17', '18'])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.60         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.41/0.60      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.41/0.60  thf(t142_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.41/0.60       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.41/0.60            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.41/0.60            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.41/0.60            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.41/0.60            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.41/0.60            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.60         (((X10) = (k1_enumset1 @ X7 @ X8 @ X9))
% 0.41/0.60          | ((X10) = (k2_tarski @ X7 @ X9))
% 0.41/0.60          | ((X10) = (k2_tarski @ X8 @ X9))
% 0.41/0.60          | ((X10) = (k2_tarski @ X7 @ X8))
% 0.41/0.60          | ((X10) = (k1_tarski @ X9))
% 0.41/0.60          | ((X10) = (k1_tarski @ X8))
% 0.41/0.60          | ((X10) = (k1_tarski @ X7))
% 0.41/0.60          | ((X10) = (k1_xboole_0))
% 0.41/0.60          | ~ (r1_tarski @ X10 @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.60         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 0.41/0.60          | ((X3) = (k1_xboole_0))
% 0.41/0.60          | ((X3) = (k1_tarski @ X2))
% 0.41/0.60          | ((X3) = (k1_tarski @ X1))
% 0.41/0.60          | ((X3) = (k1_tarski @ X0))
% 0.41/0.60          | ((X3) = (k2_tarski @ X2 @ X1))
% 0.41/0.60          | ((X3) = (k2_tarski @ X1 @ X0))
% 0.41/0.60          | ((X3) = (k2_tarski @ X2 @ X0))
% 0.41/0.60          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.41/0.60          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 0.41/0.60          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.41/0.60          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.41/0.60          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.41/0.60          | ((X1) = (k1_tarski @ X0))
% 0.41/0.60          | ((X1) = (k1_tarski @ X0))
% 0.41/0.60          | ((X1) = (k1_tarski @ X0))
% 0.41/0.60          | ((X1) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['19', '22'])).
% 0.41/0.60  thf('24', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i]:
% 0.41/0.60         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.41/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.41/0.60          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.41/0.60          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.41/0.60          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.41/0.60          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.41/0.60          | ((X1) = (k1_tarski @ X0))
% 0.41/0.60          | ((X1) = (k1_tarski @ X0))
% 0.41/0.60          | ((X1) = (k1_tarski @ X0))
% 0.41/0.60          | ((X1) = (k1_xboole_0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (((X1) = (k1_xboole_0))
% 0.41/0.60          | ((X1) = (k1_tarski @ X0))
% 0.41/0.60          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.41/0.60          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['25'])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      ((((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A))
% 0.41/0.60        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.41/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['14', '26'])).
% 0.41/0.60  thf('28', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.41/0.60        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.41/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['27', '28'])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.41/0.60        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['29'])).
% 0.41/0.60  thf(t14_funct_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.60       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.41/0.60         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X22 : $i, X23 : $i]:
% 0.41/0.60         (((k1_relat_1 @ X23) != (k1_tarski @ X22))
% 0.41/0.60          | ((k2_relat_1 @ X23) = (k1_tarski @ (k1_funct_1 @ X23 @ X22)))
% 0.41/0.60          | ~ (v1_funct_1 @ X23)
% 0.41/0.60          | ~ (v1_relat_1 @ X23))),
% 0.41/0.60      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.41/0.60          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.41/0.60        | ~ (v1_funct_1 @ sk_D)
% 0.41/0.60        | ~ (v1_relat_1 @ sk_D)
% 0.41/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.41/0.60      inference('eq_res', [status(thm)], ['32'])).
% 0.41/0.60  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(cc1_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60       ( v1_relat_1 @ C ) ))).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.41/0.60         ((v1_relat_1 @ X24)
% 0.41/0.60          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.41/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.60  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.41/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['33', '34', '37'])).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.41/0.60          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.41/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['5', '40'])).
% 0.41/0.60  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.60  thf('43', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.41/0.60      inference('demod', [status(thm)], ['41', '42'])).
% 0.41/0.60  thf(t151_relat_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( v1_relat_1 @ B ) =>
% 0.41/0.60       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.41/0.60         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      (![X18 : $i, X19 : $i]:
% 0.41/0.60         (~ (r1_xboole_0 @ (k1_relat_1 @ X18) @ X19)
% 0.41/0.60          | ((k9_relat_1 @ X18 @ X19) = (k1_xboole_0))
% 0.41/0.60          | ~ (v1_relat_1 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ sk_D)
% 0.41/0.60          | ((k9_relat_1 @ sk_D @ X0) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.41/0.60  thf(t150_relat_1, axiom,
% 0.41/0.60    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      (![X17 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 0.41/0.60      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      (![X18 : $i, X19 : $i]:
% 0.41/0.60         (((k9_relat_1 @ X18 @ X19) != (k1_xboole_0))
% 0.41/0.60          | (r1_xboole_0 @ (k1_relat_1 @ X18) @ X19)
% 0.41/0.60          | ~ (v1_relat_1 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k1_xboole_0) != (k1_xboole_0))
% 0.41/0.60          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.41/0.60          | (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.60  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.41/0.60  thf('49', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.60      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.41/0.60  thf(fc3_funct_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.41/0.60       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.41/0.60  thf('50', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.60  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.41/0.60      inference('sup+', [status(thm)], ['49', '50'])).
% 0.41/0.60  thf(t60_relat_1, axiom,
% 0.41/0.60    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.41/0.60     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.41/0.60  thf('52', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.41/0.60  thf('53', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['48', '51', '52'])).
% 0.41/0.60  thf('54', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.41/0.60      inference('simplify', [status(thm)], ['53'])).
% 0.41/0.60  thf('55', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.60  thf('56', plain, (![X0 : $i]: ((k9_relat_1 @ sk_D @ X0) = (k1_xboole_0))),
% 0.41/0.60      inference('demod', [status(thm)], ['45', '54', '55'])).
% 0.41/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.60  thf('57', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.41/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.60  thf('58', plain, ($false),
% 0.41/0.60      inference('demod', [status(thm)], ['4', '56', '57'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
