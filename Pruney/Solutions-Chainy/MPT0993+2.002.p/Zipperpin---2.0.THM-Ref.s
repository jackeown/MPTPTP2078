%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QWEoELTHo5

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:45 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 149 expanded)
%              Number of leaves         :   38 (  60 expanded)
%              Depth                    :   19
%              Number of atoms          :  705 (1638 expanded)
%              Number of equality atoms :   47 (  59 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(t40_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ A @ C )
       => ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ A @ C )
         => ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ( ( k2_partfun1 @ X33 @ X34 @ X32 @ X35 )
        = ( k7_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( v4_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6
        = ( k7_relat_1 @ X6 @ X7 ) )
      | ~ ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('28',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('35',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('39',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('41',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['39','43'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('45',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X23 )
      | ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['22','23'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_D ) ) ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['7','49'])).

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,(
    v4_relat_1 @ sk_D @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6
        = ( k7_relat_1 @ X6 @ X7 ) )
      | ~ ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['22','23'])).

thf('56',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['40','42'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['6','56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QWEoELTHo5
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.58/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.76  % Solved by: fo/fo7.sh
% 0.58/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.76  % done 328 iterations in 0.317s
% 0.58/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.76  % SZS output start Refutation
% 0.58/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.76  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.58/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.76  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.58/0.76  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.58/0.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.58/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.76  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.58/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.58/0.76  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.58/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.76  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.58/0.76  thf(t40_funct_2, conjecture,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.76       ( ( r1_tarski @ A @ C ) =>
% 0.58/0.76         ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ))).
% 0.58/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.76    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.76            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.76          ( ( r1_tarski @ A @ C ) =>
% 0.58/0.76            ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )),
% 0.58/0.76    inference('cnf.neg', [status(esa)], [t40_funct_2])).
% 0.58/0.76  thf('0', plain,
% 0.58/0.76      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.58/0.76          (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_D)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('1', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(redefinition_k2_partfun1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76     ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.76       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.58/0.76  thf('2', plain,
% 0.58/0.76      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.58/0.76          | ~ (v1_funct_1 @ X32)
% 0.58/0.76          | ((k2_partfun1 @ X33 @ X34 @ X32 @ X35) = (k7_relat_1 @ X32 @ X35)))),
% 0.58/0.76      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.58/0.76  thf('3', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 0.58/0.76          | ~ (v1_funct_1 @ sk_D))),
% 0.58/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.76  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('5', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['3', '4'])).
% 0.58/0.76  thf('6', plain,
% 0.58/0.76      (~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.58/0.76      inference('demod', [status(thm)], ['0', '5'])).
% 0.58/0.76  thf('7', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(d10_xboole_0, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.76  thf('8', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.58/0.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.76  thf('9', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.58/0.76      inference('simplify', [status(thm)], ['8'])).
% 0.58/0.76  thf(d1_funct_2, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.76       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.76           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.58/0.76             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.58/0.76         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.76           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.58/0.76             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.58/0.76  thf(zf_stmt_1, axiom,
% 0.58/0.76    (![B:$i,A:$i]:
% 0.58/0.76     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.76       ( zip_tseitin_0 @ B @ A ) ))).
% 0.58/0.76  thf('10', plain,
% 0.58/0.76      (![X24 : $i, X25 : $i]:
% 0.58/0.76         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.76  thf(t113_zfmisc_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.58/0.76       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.58/0.76  thf('11', plain,
% 0.58/0.76      (![X4 : $i, X5 : $i]:
% 0.58/0.76         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.58/0.76  thf('12', plain,
% 0.58/0.76      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.76      inference('simplify', [status(thm)], ['11'])).
% 0.58/0.76  thf('13', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.76         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.58/0.76      inference('sup+', [status(thm)], ['10', '12'])).
% 0.58/0.76  thf('14', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('15', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.58/0.76          | (zip_tseitin_0 @ sk_B @ X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.58/0.76  thf('16', plain,
% 0.58/0.76      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.76      inference('simplify', [status(thm)], ['11'])).
% 0.58/0.76  thf(cc2_relset_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.58/0.76  thf('17', plain,
% 0.58/0.76      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.58/0.76         ((v4_relat_1 @ X11 @ X12)
% 0.58/0.76          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.58/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.58/0.76  thf('18', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.58/0.76          | (v4_relat_1 @ X1 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.76  thf('19', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((zip_tseitin_0 @ sk_B @ X1) | (v4_relat_1 @ sk_D @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['15', '18'])).
% 0.58/0.76  thf(t209_relat_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.58/0.76       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.58/0.76  thf('20', plain,
% 0.58/0.76      (![X6 : $i, X7 : $i]:
% 0.58/0.76         (((X6) = (k7_relat_1 @ X6 @ X7))
% 0.58/0.76          | ~ (v4_relat_1 @ X6 @ X7)
% 0.58/0.76          | ~ (v1_relat_1 @ X6))),
% 0.58/0.76      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.58/0.76  thf('21', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((zip_tseitin_0 @ sk_B @ X1)
% 0.58/0.76          | ~ (v1_relat_1 @ sk_D)
% 0.58/0.76          | ((sk_D) = (k7_relat_1 @ sk_D @ X0)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['19', '20'])).
% 0.58/0.76  thf('22', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(cc1_relset_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.76       ( v1_relat_1 @ C ) ))).
% 0.58/0.76  thf('23', plain,
% 0.58/0.76      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.58/0.76         ((v1_relat_1 @ X8)
% 0.58/0.76          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.58/0.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.58/0.76  thf('24', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.58/0.76  thf('25', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((zip_tseitin_0 @ sk_B @ X1) | ((sk_D) = (k7_relat_1 @ sk_D @ X0)))),
% 0.58/0.76      inference('demod', [status(thm)], ['21', '24'])).
% 0.58/0.76  thf('26', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.58/0.76  thf(zf_stmt_3, axiom,
% 0.58/0.76    (![C:$i,B:$i,A:$i]:
% 0.58/0.76     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.58/0.76       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.58/0.76  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.58/0.76  thf(zf_stmt_5, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.76       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.58/0.76         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.76           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.58/0.76             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.58/0.76  thf('27', plain,
% 0.58/0.76      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.58/0.76         (~ (zip_tseitin_0 @ X29 @ X30)
% 0.58/0.76          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 0.58/0.76          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.76  thf('28', plain,
% 0.58/0.76      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['26', '27'])).
% 0.58/0.76  thf('29', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (((sk_D) = (k7_relat_1 @ sk_D @ X0))
% 0.58/0.76          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['25', '28'])).
% 0.58/0.76  thf('30', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('31', plain,
% 0.58/0.76      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.58/0.76         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.58/0.76          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 0.58/0.76          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.76  thf('32', plain,
% 0.58/0.76      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.58/0.76        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['30', '31'])).
% 0.58/0.76  thf('33', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(redefinition_k1_relset_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.76       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.58/0.76  thf('34', plain,
% 0.58/0.76      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.76         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.58/0.76          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.58/0.76      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.58/0.76  thf('35', plain,
% 0.58/0.76      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.58/0.76      inference('sup-', [status(thm)], ['33', '34'])).
% 0.58/0.76  thf('36', plain,
% 0.58/0.76      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.58/0.76      inference('demod', [status(thm)], ['32', '35'])).
% 0.58/0.76  thf('37', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (((sk_D) = (k7_relat_1 @ sk_D @ X0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['29', '36'])).
% 0.58/0.76  thf('38', plain,
% 0.58/0.76      (~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.58/0.76      inference('demod', [status(thm)], ['0', '5'])).
% 0.58/0.76  thf('39', plain,
% 0.58/0.76      ((~ (r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)
% 0.58/0.76        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['37', '38'])).
% 0.58/0.76  thf('40', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(redefinition_r2_relset_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.76       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.58/0.76  thf('41', plain,
% 0.58/0.76      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.58/0.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.58/0.76          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 0.58/0.76          | ((X17) != (X20)))),
% 0.58/0.76      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.58/0.76  thf('42', plain,
% 0.58/0.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.76         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 0.58/0.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.58/0.76      inference('simplify', [status(thm)], ['41'])).
% 0.58/0.76  thf('43', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.58/0.76      inference('sup-', [status(thm)], ['40', '42'])).
% 0.58/0.76  thf('44', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.58/0.76      inference('demod', [status(thm)], ['39', '43'])).
% 0.58/0.76  thf(t11_relset_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( v1_relat_1 @ C ) =>
% 0.58/0.76       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.58/0.76           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.58/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.58/0.76  thf('45', plain,
% 0.58/0.76      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.58/0.76         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 0.58/0.76          | ~ (r1_tarski @ (k2_relat_1 @ X21) @ X23)
% 0.58/0.76          | (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.58/0.76          | ~ (v1_relat_1 @ X21))),
% 0.58/0.76      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.58/0.76  thf('46', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         (~ (r1_tarski @ sk_A @ X0)
% 0.58/0.76          | ~ (v1_relat_1 @ sk_D)
% 0.58/0.76          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.58/0.76          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['44', '45'])).
% 0.58/0.76  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.58/0.76  thf('48', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         (~ (r1_tarski @ sk_A @ X0)
% 0.58/0.76          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.58/0.76          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X1))),
% 0.58/0.76      inference('demod', [status(thm)], ['46', '47'])).
% 0.58/0.76  thf('49', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((m1_subset_1 @ sk_D @ 
% 0.58/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_D))))
% 0.58/0.76          | ~ (r1_tarski @ sk_A @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['9', '48'])).
% 0.58/0.76  thf('50', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ 
% 0.58/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ (k2_relat_1 @ sk_D))))),
% 0.58/0.76      inference('sup-', [status(thm)], ['7', '49'])).
% 0.58/0.76  thf('51', plain,
% 0.58/0.76      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.58/0.76         ((v4_relat_1 @ X11 @ X12)
% 0.58/0.76          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.58/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.58/0.76  thf('52', plain, ((v4_relat_1 @ sk_D @ sk_C)),
% 0.58/0.76      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.76  thf('53', plain,
% 0.58/0.76      (![X6 : $i, X7 : $i]:
% 0.58/0.76         (((X6) = (k7_relat_1 @ X6 @ X7))
% 0.58/0.76          | ~ (v4_relat_1 @ X6 @ X7)
% 0.58/0.76          | ~ (v1_relat_1 @ X6))),
% 0.58/0.76      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.58/0.76  thf('54', plain,
% 0.58/0.76      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_C)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['52', '53'])).
% 0.58/0.76  thf('55', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.58/0.76  thf('56', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_C))),
% 0.58/0.76      inference('demod', [status(thm)], ['54', '55'])).
% 0.58/0.76  thf('57', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.58/0.76      inference('sup-', [status(thm)], ['40', '42'])).
% 0.58/0.76  thf('58', plain, ($false),
% 0.58/0.76      inference('demod', [status(thm)], ['6', '56', '57'])).
% 0.58/0.76  
% 0.58/0.76  % SZS output end Refutation
% 0.58/0.76  
% 0.60/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
