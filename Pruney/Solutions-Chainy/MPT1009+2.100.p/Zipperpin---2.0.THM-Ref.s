%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VT484mhjoF

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:03 EST 2020

% Result     : Theorem 4.15s
% Output     : Refutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 207 expanded)
%              Number of leaves         :   37 (  77 expanded)
%              Depth                    :   19
%              Number of atoms          :  791 (2645 expanded)
%              Number of equality atoms :   97 ( 231 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k7_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k9_relat_1 @ X30 @ X33 ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X24 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != ( k1_tarski @ X19 ) )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_tarski @ ( k1_funct_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('44',plain,(
    ! [X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['35','36'])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('49',plain,(
    ! [X17: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('50',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['4','48','49','50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VT484mhjoF
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.15/4.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.15/4.35  % Solved by: fo/fo7.sh
% 4.15/4.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.15/4.35  % done 2170 iterations in 3.895s
% 4.15/4.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.15/4.35  % SZS output start Refutation
% 4.15/4.35  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 4.15/4.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.15/4.35  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.15/4.35  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.15/4.35  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 4.15/4.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.15/4.35  thf(sk_A_type, type, sk_A: $i).
% 4.15/4.35  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.15/4.35  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.15/4.35  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 4.15/4.35  thf(sk_D_type, type, sk_D: $i).
% 4.15/4.35  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.15/4.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.15/4.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.15/4.35  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.15/4.35  thf(sk_C_type, type, sk_C: $i).
% 4.15/4.35  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.15/4.35  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.15/4.35  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 4.15/4.35  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.15/4.35  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 4.15/4.35  thf(sk_B_type, type, sk_B: $i).
% 4.15/4.35  thf(t64_funct_2, conjecture,
% 4.15/4.35    (![A:$i,B:$i,C:$i,D:$i]:
% 4.15/4.35     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 4.15/4.35         ( m1_subset_1 @
% 4.15/4.35           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 4.15/4.35       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 4.15/4.35         ( r1_tarski @
% 4.15/4.35           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 4.15/4.35           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 4.15/4.35  thf(zf_stmt_0, negated_conjecture,
% 4.15/4.35    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.15/4.35        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 4.15/4.35            ( m1_subset_1 @
% 4.15/4.35              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 4.15/4.35          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 4.15/4.35            ( r1_tarski @
% 4.15/4.35              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 4.15/4.35              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 4.15/4.35    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 4.15/4.35  thf('0', plain,
% 4.15/4.35      (~ (r1_tarski @ 
% 4.15/4.35          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 4.15/4.35          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 4.15/4.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.15/4.35  thf('1', plain,
% 4.15/4.35      ((m1_subset_1 @ sk_D @ 
% 4.15/4.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.15/4.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.15/4.35  thf(redefinition_k7_relset_1, axiom,
% 4.15/4.35    (![A:$i,B:$i,C:$i,D:$i]:
% 4.15/4.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.15/4.35       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 4.15/4.35  thf('2', plain,
% 4.15/4.35      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 4.15/4.35         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 4.15/4.35          | ((k7_relset_1 @ X31 @ X32 @ X30 @ X33) = (k9_relat_1 @ X30 @ X33)))),
% 4.15/4.35      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 4.15/4.35  thf('3', plain,
% 4.15/4.35      (![X0 : $i]:
% 4.15/4.35         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 4.15/4.35           = (k9_relat_1 @ sk_D @ X0))),
% 4.15/4.35      inference('sup-', [status(thm)], ['1', '2'])).
% 4.15/4.35  thf('4', plain,
% 4.15/4.35      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 4.15/4.35          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 4.15/4.35      inference('demod', [status(thm)], ['0', '3'])).
% 4.15/4.35  thf(t144_relat_1, axiom,
% 4.15/4.35    (![A:$i,B:$i]:
% 4.15/4.35     ( ( v1_relat_1 @ B ) =>
% 4.15/4.35       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 4.15/4.35  thf('5', plain,
% 4.15/4.35      (![X15 : $i, X16 : $i]:
% 4.15/4.35         ((r1_tarski @ (k9_relat_1 @ X15 @ X16) @ (k2_relat_1 @ X15))
% 4.15/4.35          | ~ (v1_relat_1 @ X15))),
% 4.15/4.35      inference('cnf', [status(esa)], [t144_relat_1])).
% 4.15/4.35  thf('6', plain,
% 4.15/4.35      ((m1_subset_1 @ sk_D @ 
% 4.15/4.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.15/4.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.15/4.35  thf(dt_k1_relset_1, axiom,
% 4.15/4.35    (![A:$i,B:$i,C:$i]:
% 4.15/4.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.15/4.35       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.15/4.35  thf('7', plain,
% 4.15/4.35      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.15/4.35         ((m1_subset_1 @ (k1_relset_1 @ X24 @ X25 @ X26) @ (k1_zfmisc_1 @ X24))
% 4.15/4.35          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 4.15/4.35      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 4.15/4.35  thf('8', plain,
% 4.15/4.35      ((m1_subset_1 @ (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) @ 
% 4.15/4.35        (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 4.15/4.35      inference('sup-', [status(thm)], ['6', '7'])).
% 4.15/4.35  thf('9', plain,
% 4.15/4.35      ((m1_subset_1 @ sk_D @ 
% 4.15/4.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.15/4.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.15/4.35  thf(redefinition_k1_relset_1, axiom,
% 4.15/4.35    (![A:$i,B:$i,C:$i]:
% 4.15/4.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.15/4.35       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.15/4.35  thf('10', plain,
% 4.15/4.35      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.15/4.35         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 4.15/4.35          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 4.15/4.35      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.15/4.35  thf('11', plain,
% 4.15/4.35      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 4.15/4.35      inference('sup-', [status(thm)], ['9', '10'])).
% 4.15/4.35  thf('12', plain,
% 4.15/4.35      ((m1_subset_1 @ (k1_relat_1 @ sk_D) @ (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 4.15/4.35      inference('demod', [status(thm)], ['8', '11'])).
% 4.15/4.35  thf(t3_subset, axiom,
% 4.15/4.35    (![A:$i,B:$i]:
% 4.15/4.35     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.15/4.35  thf('13', plain,
% 4.15/4.35      (![X12 : $i, X13 : $i]:
% 4.15/4.35         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 4.15/4.35      inference('cnf', [status(esa)], [t3_subset])).
% 4.15/4.35  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 4.15/4.35      inference('sup-', [status(thm)], ['12', '13'])).
% 4.15/4.35  thf(t71_enumset1, axiom,
% 4.15/4.35    (![A:$i,B:$i,C:$i]:
% 4.15/4.35     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 4.15/4.35  thf('15', plain,
% 4.15/4.35      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.15/4.35         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 4.15/4.35      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.15/4.35  thf(t70_enumset1, axiom,
% 4.15/4.35    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 4.15/4.35  thf('16', plain,
% 4.15/4.35      (![X2 : $i, X3 : $i]:
% 4.15/4.35         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 4.15/4.35      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.15/4.35  thf('17', plain,
% 4.15/4.35      (![X0 : $i, X1 : $i]:
% 4.15/4.35         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 4.15/4.35      inference('sup+', [status(thm)], ['15', '16'])).
% 4.15/4.35  thf(t69_enumset1, axiom,
% 4.15/4.35    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.15/4.35  thf('18', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 4.15/4.35      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.15/4.35  thf('19', plain,
% 4.15/4.35      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 4.15/4.35      inference('sup+', [status(thm)], ['17', '18'])).
% 4.15/4.35  thf('20', plain,
% 4.15/4.35      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.15/4.35         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 4.15/4.35      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.15/4.35  thf(t142_zfmisc_1, axiom,
% 4.15/4.35    (![A:$i,B:$i,C:$i,D:$i]:
% 4.15/4.35     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 4.15/4.35       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 4.15/4.35            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 4.15/4.35            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 4.15/4.35            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 4.15/4.35            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 4.15/4.35            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 4.15/4.35  thf('21', plain,
% 4.15/4.35      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 4.15/4.35         (((X10) = (k1_enumset1 @ X7 @ X8 @ X9))
% 4.15/4.35          | ((X10) = (k2_tarski @ X7 @ X9))
% 4.15/4.35          | ((X10) = (k2_tarski @ X8 @ X9))
% 4.15/4.35          | ((X10) = (k2_tarski @ X7 @ X8))
% 4.15/4.35          | ((X10) = (k1_tarski @ X9))
% 4.15/4.35          | ((X10) = (k1_tarski @ X8))
% 4.15/4.35          | ((X10) = (k1_tarski @ X7))
% 4.15/4.35          | ((X10) = (k1_xboole_0))
% 4.15/4.35          | ~ (r1_tarski @ X10 @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 4.15/4.35      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 4.15/4.35  thf('22', plain,
% 4.15/4.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.15/4.35         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 4.15/4.35          | ((X3) = (k1_xboole_0))
% 4.15/4.35          | ((X3) = (k1_tarski @ X2))
% 4.15/4.35          | ((X3) = (k1_tarski @ X1))
% 4.15/4.35          | ((X3) = (k1_tarski @ X0))
% 4.15/4.35          | ((X3) = (k2_tarski @ X2 @ X1))
% 4.15/4.35          | ((X3) = (k2_tarski @ X1 @ X0))
% 4.15/4.35          | ((X3) = (k2_tarski @ X2 @ X0))
% 4.15/4.35          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 4.15/4.35      inference('sup-', [status(thm)], ['20', '21'])).
% 4.15/4.35  thf('23', plain,
% 4.15/4.35      (![X0 : $i, X1 : $i]:
% 4.15/4.35         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 4.15/4.35          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 4.15/4.35          | ((X1) = (k2_tarski @ X0 @ X0))
% 4.15/4.35          | ((X1) = (k2_tarski @ X0 @ X0))
% 4.15/4.35          | ((X1) = (k2_tarski @ X0 @ X0))
% 4.15/4.35          | ((X1) = (k1_tarski @ X0))
% 4.15/4.35          | ((X1) = (k1_tarski @ X0))
% 4.15/4.35          | ((X1) = (k1_tarski @ X0))
% 4.15/4.35          | ((X1) = (k1_xboole_0)))),
% 4.15/4.35      inference('sup-', [status(thm)], ['19', '22'])).
% 4.15/4.35  thf('24', plain,
% 4.15/4.35      (![X2 : $i, X3 : $i]:
% 4.15/4.35         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 4.15/4.35      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.15/4.35  thf('25', plain,
% 4.15/4.35      (![X0 : $i, X1 : $i]:
% 4.15/4.35         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 4.15/4.35          | ((X1) = (k2_tarski @ X0 @ X0))
% 4.15/4.35          | ((X1) = (k2_tarski @ X0 @ X0))
% 4.15/4.35          | ((X1) = (k2_tarski @ X0 @ X0))
% 4.15/4.35          | ((X1) = (k2_tarski @ X0 @ X0))
% 4.15/4.35          | ((X1) = (k1_tarski @ X0))
% 4.15/4.35          | ((X1) = (k1_tarski @ X0))
% 4.15/4.35          | ((X1) = (k1_tarski @ X0))
% 4.15/4.35          | ((X1) = (k1_xboole_0)))),
% 4.15/4.35      inference('demod', [status(thm)], ['23', '24'])).
% 4.15/4.35  thf('26', plain,
% 4.15/4.35      (![X0 : $i, X1 : $i]:
% 4.15/4.35         (((X1) = (k1_xboole_0))
% 4.15/4.35          | ((X1) = (k1_tarski @ X0))
% 4.15/4.35          | ((X1) = (k2_tarski @ X0 @ X0))
% 4.15/4.35          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 4.15/4.35      inference('simplify', [status(thm)], ['25'])).
% 4.15/4.35  thf('27', plain,
% 4.15/4.35      ((((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A))
% 4.15/4.35        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 4.15/4.35        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 4.15/4.35      inference('sup-', [status(thm)], ['14', '26'])).
% 4.15/4.35  thf('28', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 4.15/4.35      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.15/4.35  thf('29', plain,
% 4.15/4.35      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 4.15/4.35        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 4.15/4.35        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 4.15/4.35      inference('demod', [status(thm)], ['27', '28'])).
% 4.15/4.35  thf('30', plain,
% 4.15/4.35      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 4.15/4.35        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 4.15/4.35      inference('simplify', [status(thm)], ['29'])).
% 4.15/4.35  thf(t14_funct_1, axiom,
% 4.15/4.35    (![A:$i,B:$i]:
% 4.15/4.35     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.15/4.35       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 4.15/4.35         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 4.15/4.35  thf('31', plain,
% 4.15/4.35      (![X19 : $i, X20 : $i]:
% 4.15/4.35         (((k1_relat_1 @ X20) != (k1_tarski @ X19))
% 4.15/4.35          | ((k2_relat_1 @ X20) = (k1_tarski @ (k1_funct_1 @ X20 @ X19)))
% 4.15/4.35          | ~ (v1_funct_1 @ X20)
% 4.15/4.35          | ~ (v1_relat_1 @ X20))),
% 4.15/4.35      inference('cnf', [status(esa)], [t14_funct_1])).
% 4.15/4.35  thf('32', plain,
% 4.15/4.35      (![X0 : $i]:
% 4.15/4.35         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 4.15/4.35          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 4.15/4.35          | ~ (v1_relat_1 @ X0)
% 4.15/4.35          | ~ (v1_funct_1 @ X0)
% 4.15/4.35          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 4.15/4.35      inference('sup-', [status(thm)], ['30', '31'])).
% 4.15/4.35  thf('33', plain,
% 4.15/4.35      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 4.15/4.35        | ~ (v1_funct_1 @ sk_D)
% 4.15/4.35        | ~ (v1_relat_1 @ sk_D)
% 4.15/4.35        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 4.15/4.35      inference('eq_res', [status(thm)], ['32'])).
% 4.15/4.35  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 4.15/4.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.15/4.35  thf('35', plain,
% 4.15/4.35      ((m1_subset_1 @ sk_D @ 
% 4.15/4.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.15/4.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.15/4.35  thf(cc1_relset_1, axiom,
% 4.15/4.35    (![A:$i,B:$i,C:$i]:
% 4.15/4.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.15/4.35       ( v1_relat_1 @ C ) ))).
% 4.15/4.35  thf('36', plain,
% 4.15/4.35      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.15/4.35         ((v1_relat_1 @ X21)
% 4.15/4.35          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.15/4.35      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.15/4.35  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 4.15/4.35      inference('sup-', [status(thm)], ['35', '36'])).
% 4.15/4.35  thf('38', plain,
% 4.15/4.35      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 4.15/4.35        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 4.15/4.35      inference('demod', [status(thm)], ['33', '34', '37'])).
% 4.15/4.35  thf('39', plain,
% 4.15/4.35      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 4.15/4.35          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 4.15/4.35      inference('demod', [status(thm)], ['0', '3'])).
% 4.15/4.35  thf('40', plain,
% 4.15/4.35      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 4.15/4.35        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 4.15/4.35      inference('sup-', [status(thm)], ['38', '39'])).
% 4.15/4.35  thf('41', plain,
% 4.15/4.35      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 4.15/4.35      inference('sup-', [status(thm)], ['5', '40'])).
% 4.15/4.35  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 4.15/4.35      inference('sup-', [status(thm)], ['35', '36'])).
% 4.15/4.35  thf('43', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 4.15/4.35      inference('demod', [status(thm)], ['41', '42'])).
% 4.15/4.35  thf(t64_relat_1, axiom,
% 4.15/4.35    (![A:$i]:
% 4.15/4.35     ( ( v1_relat_1 @ A ) =>
% 4.15/4.35       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 4.15/4.35           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 4.15/4.35         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 4.15/4.35  thf('44', plain,
% 4.15/4.35      (![X18 : $i]:
% 4.15/4.35         (((k1_relat_1 @ X18) != (k1_xboole_0))
% 4.15/4.35          | ((X18) = (k1_xboole_0))
% 4.15/4.35          | ~ (v1_relat_1 @ X18))),
% 4.15/4.35      inference('cnf', [status(esa)], [t64_relat_1])).
% 4.15/4.35  thf('45', plain,
% 4.15/4.35      ((((k1_xboole_0) != (k1_xboole_0))
% 4.15/4.35        | ~ (v1_relat_1 @ sk_D)
% 4.15/4.35        | ((sk_D) = (k1_xboole_0)))),
% 4.15/4.35      inference('sup-', [status(thm)], ['43', '44'])).
% 4.15/4.35  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 4.15/4.35      inference('sup-', [status(thm)], ['35', '36'])).
% 4.15/4.35  thf('47', plain,
% 4.15/4.35      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 4.15/4.35      inference('demod', [status(thm)], ['45', '46'])).
% 4.15/4.35  thf('48', plain, (((sk_D) = (k1_xboole_0))),
% 4.15/4.35      inference('simplify', [status(thm)], ['47'])).
% 4.15/4.35  thf(t150_relat_1, axiom,
% 4.15/4.35    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 4.15/4.35  thf('49', plain,
% 4.15/4.35      (![X17 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 4.15/4.35      inference('cnf', [status(esa)], [t150_relat_1])).
% 4.15/4.35  thf('50', plain, (((sk_D) = (k1_xboole_0))),
% 4.15/4.35      inference('simplify', [status(thm)], ['47'])).
% 4.15/4.35  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.15/4.35  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.15/4.35      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.15/4.35  thf('52', plain, ($false),
% 4.15/4.35      inference('demod', [status(thm)], ['4', '48', '49', '50', '51'])).
% 4.15/4.35  
% 4.15/4.35  % SZS output end Refutation
% 4.15/4.35  
% 4.15/4.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
