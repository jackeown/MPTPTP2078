%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ROGq6101jp

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:41 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 160 expanded)
%              Number of leaves         :   38 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  887 (3288 expanded)
%              Number of equality atoms :   58 ( 241 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(t20_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( ( k2_relset_1 @ B @ C @ E )
                = C ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ D )
                  = B )
                & ( ( k2_relset_1 @ B @ C @ E )
                  = C ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('10',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','7','16'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('22',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['22','29','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) )
        = ( k2_relat_1 @ X6 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X6 ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      = ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('46',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('48',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('58',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['45','50','55','58'])).

thf('60',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['19','59'])).

thf('61',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('63',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ROGq6101jp
% 0.12/0.31  % Computer   : n022.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 14:42:41 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.31  % Running portfolio for 600 s
% 0.12/0.31  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.31  % Number of cores: 8
% 0.16/0.31  % Python version: Python 3.6.8
% 0.16/0.32  % Running in FO mode
% 1.63/1.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.63/1.88  % Solved by: fo/fo7.sh
% 1.63/1.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.63/1.88  % done 762 iterations in 1.460s
% 1.63/1.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.63/1.88  % SZS output start Refutation
% 1.63/1.88  thf(sk_B_type, type, sk_B: $i).
% 1.63/1.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.63/1.88  thf(sk_C_type, type, sk_C: $i).
% 1.63/1.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.63/1.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.63/1.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.63/1.88  thf(sk_A_type, type, sk_A: $i).
% 1.63/1.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.63/1.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.63/1.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.63/1.88  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.63/1.88  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.63/1.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.63/1.88  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.63/1.88  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.63/1.88  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.63/1.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.63/1.88  thf(sk_D_type, type, sk_D: $i).
% 1.63/1.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.63/1.88  thf(sk_E_type, type, sk_E: $i).
% 1.63/1.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.63/1.88  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.63/1.88  thf(t20_funct_2, conjecture,
% 1.63/1.88    (![A:$i,B:$i,C:$i,D:$i]:
% 1.63/1.88     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.63/1.88         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.63/1.88       ( ![E:$i]:
% 1.63/1.88         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.63/1.88             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.63/1.88           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.63/1.88               ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 1.63/1.88             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.63/1.88               ( ( k2_relset_1 @
% 1.63/1.88                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.63/1.88                 ( C ) ) ) ) ) ) ))).
% 1.63/1.88  thf(zf_stmt_0, negated_conjecture,
% 1.63/1.88    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.63/1.88        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.63/1.88            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.63/1.88          ( ![E:$i]:
% 1.63/1.88            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.63/1.88                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.63/1.88              ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.63/1.88                  ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 1.63/1.88                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.63/1.88                  ( ( k2_relset_1 @
% 1.63/1.88                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.63/1.88                    ( C ) ) ) ) ) ) ) )),
% 1.63/1.88    inference('cnf.neg', [status(esa)], [t20_funct_2])).
% 1.63/1.88  thf('0', plain,
% 1.63/1.88      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf('1', plain,
% 1.63/1.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf(dt_k1_partfun1, axiom,
% 1.63/1.88    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.63/1.88     ( ( ( v1_funct_1 @ E ) & 
% 1.63/1.88         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.63/1.88         ( v1_funct_1 @ F ) & 
% 1.63/1.88         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.63/1.88       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.63/1.88         ( m1_subset_1 @
% 1.63/1.88           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.63/1.88           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.63/1.88  thf('2', plain,
% 1.63/1.88      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.63/1.88         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.63/1.88          | ~ (v1_funct_1 @ X24)
% 1.63/1.88          | ~ (v1_funct_1 @ X27)
% 1.63/1.88          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.63/1.88          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 1.63/1.88             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 1.63/1.88      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.63/1.88  thf('3', plain,
% 1.63/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.63/1.88         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.63/1.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.63/1.88          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.63/1.88          | ~ (v1_funct_1 @ X1)
% 1.63/1.88          | ~ (v1_funct_1 @ sk_D))),
% 1.63/1.88      inference('sup-', [status(thm)], ['1', '2'])).
% 1.63/1.88  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf('5', plain,
% 1.63/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.63/1.88         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.63/1.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.63/1.88          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.63/1.88          | ~ (v1_funct_1 @ X1))),
% 1.63/1.88      inference('demod', [status(thm)], ['3', '4'])).
% 1.63/1.88  thf('6', plain,
% 1.63/1.88      ((~ (v1_funct_1 @ sk_E)
% 1.63/1.88        | (m1_subset_1 @ 
% 1.63/1.88           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 1.63/1.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.63/1.88      inference('sup-', [status(thm)], ['0', '5'])).
% 1.63/1.88  thf('7', plain, ((v1_funct_1 @ sk_E)),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf('8', plain,
% 1.63/1.88      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf('9', plain,
% 1.63/1.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf(redefinition_k1_partfun1, axiom,
% 1.63/1.88    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.63/1.88     ( ( ( v1_funct_1 @ E ) & 
% 1.63/1.88         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.63/1.88         ( v1_funct_1 @ F ) & 
% 1.63/1.88         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.63/1.88       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.63/1.88  thf('10', plain,
% 1.63/1.88      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.63/1.88         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.63/1.88          | ~ (v1_funct_1 @ X30)
% 1.63/1.88          | ~ (v1_funct_1 @ X33)
% 1.63/1.88          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.63/1.88          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 1.63/1.88              = (k5_relat_1 @ X30 @ X33)))),
% 1.63/1.88      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.63/1.88  thf('11', plain,
% 1.63/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.63/1.88         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.63/1.88            = (k5_relat_1 @ sk_D @ X0))
% 1.63/1.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.63/1.88          | ~ (v1_funct_1 @ X0)
% 1.63/1.88          | ~ (v1_funct_1 @ sk_D))),
% 1.63/1.88      inference('sup-', [status(thm)], ['9', '10'])).
% 1.63/1.88  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf('13', plain,
% 1.63/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.63/1.88         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.63/1.88            = (k5_relat_1 @ sk_D @ X0))
% 1.63/1.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.63/1.88          | ~ (v1_funct_1 @ X0))),
% 1.63/1.88      inference('demod', [status(thm)], ['11', '12'])).
% 1.63/1.88  thf('14', plain,
% 1.63/1.88      ((~ (v1_funct_1 @ sk_E)
% 1.63/1.88        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.63/1.88            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.63/1.88      inference('sup-', [status(thm)], ['8', '13'])).
% 1.63/1.88  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf('16', plain,
% 1.63/1.88      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.63/1.88         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.63/1.88      inference('demod', [status(thm)], ['14', '15'])).
% 1.63/1.88  thf('17', plain,
% 1.63/1.88      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 1.63/1.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.63/1.88      inference('demod', [status(thm)], ['6', '7', '16'])).
% 1.63/1.88  thf(redefinition_k2_relset_1, axiom,
% 1.63/1.88    (![A:$i,B:$i,C:$i]:
% 1.63/1.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.63/1.88       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.63/1.88  thf('18', plain,
% 1.63/1.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.63/1.88         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.63/1.88          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.63/1.88      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.63/1.88  thf('19', plain,
% 1.63/1.88      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 1.63/1.88         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 1.63/1.88      inference('sup-', [status(thm)], ['17', '18'])).
% 1.63/1.88  thf('20', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf(d1_funct_2, axiom,
% 1.63/1.88    (![A:$i,B:$i,C:$i]:
% 1.63/1.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.63/1.88       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.63/1.88           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.63/1.88             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.63/1.88         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.63/1.88           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.63/1.88             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.63/1.88  thf(zf_stmt_1, axiom,
% 1.63/1.88    (![C:$i,B:$i,A:$i]:
% 1.63/1.88     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.63/1.88       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.63/1.88  thf('21', plain,
% 1.63/1.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.63/1.88         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 1.63/1.88          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 1.63/1.88          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.63/1.88  thf('22', plain,
% 1.63/1.88      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.63/1.88        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 1.63/1.88      inference('sup-', [status(thm)], ['20', '21'])).
% 1.63/1.88  thf(zf_stmt_2, axiom,
% 1.63/1.88    (![B:$i,A:$i]:
% 1.63/1.88     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.63/1.88       ( zip_tseitin_0 @ B @ A ) ))).
% 1.63/1.88  thf('23', plain,
% 1.63/1.88      (![X16 : $i, X17 : $i]:
% 1.63/1.88         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.63/1.88  thf('24', plain,
% 1.63/1.88      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.63/1.88  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.63/1.88  thf(zf_stmt_5, axiom,
% 1.63/1.88    (![A:$i,B:$i,C:$i]:
% 1.63/1.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.63/1.88       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.63/1.88         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.63/1.88           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.63/1.88             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.63/1.88  thf('25', plain,
% 1.63/1.88      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.63/1.88         (~ (zip_tseitin_0 @ X21 @ X22)
% 1.63/1.88          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 1.63/1.88          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.63/1.88  thf('26', plain,
% 1.63/1.88      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.63/1.88      inference('sup-', [status(thm)], ['24', '25'])).
% 1.63/1.88  thf('27', plain,
% 1.63/1.88      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 1.63/1.88      inference('sup-', [status(thm)], ['23', '26'])).
% 1.63/1.88  thf('28', plain, (((sk_C) != (k1_xboole_0))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf('29', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 1.63/1.88      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 1.63/1.88  thf('30', plain,
% 1.63/1.88      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf(redefinition_k1_relset_1, axiom,
% 1.63/1.88    (![A:$i,B:$i,C:$i]:
% 1.63/1.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.63/1.88       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.63/1.88  thf('31', plain,
% 1.63/1.88      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.63/1.88         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 1.63/1.88          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.63/1.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.63/1.88  thf('32', plain,
% 1.63/1.88      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.63/1.88      inference('sup-', [status(thm)], ['30', '31'])).
% 1.63/1.88  thf('33', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 1.63/1.88      inference('demod', [status(thm)], ['22', '29', '32'])).
% 1.63/1.88  thf('34', plain,
% 1.63/1.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf('35', plain,
% 1.63/1.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.63/1.88         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.63/1.88          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.63/1.88      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.63/1.88  thf('36', plain,
% 1.63/1.88      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.63/1.88      inference('sup-', [status(thm)], ['34', '35'])).
% 1.63/1.88  thf('37', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf('38', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 1.63/1.88      inference('sup+', [status(thm)], ['36', '37'])).
% 1.63/1.88  thf(t47_relat_1, axiom,
% 1.63/1.88    (![A:$i]:
% 1.63/1.88     ( ( v1_relat_1 @ A ) =>
% 1.63/1.88       ( ![B:$i]:
% 1.63/1.88         ( ( v1_relat_1 @ B ) =>
% 1.63/1.88           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 1.63/1.88             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.63/1.88  thf('39', plain,
% 1.63/1.88      (![X5 : $i, X6 : $i]:
% 1.63/1.88         (~ (v1_relat_1 @ X5)
% 1.63/1.88          | ((k2_relat_1 @ (k5_relat_1 @ X5 @ X6)) = (k2_relat_1 @ X6))
% 1.63/1.88          | ~ (r1_tarski @ (k1_relat_1 @ X6) @ (k2_relat_1 @ X5))
% 1.63/1.88          | ~ (v1_relat_1 @ X6))),
% 1.63/1.88      inference('cnf', [status(esa)], [t47_relat_1])).
% 1.63/1.88  thf('40', plain,
% 1.63/1.88      (![X0 : $i]:
% 1.63/1.88         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 1.63/1.88          | ~ (v1_relat_1 @ X0)
% 1.63/1.88          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ X0))
% 1.63/1.88          | ~ (v1_relat_1 @ sk_D))),
% 1.63/1.88      inference('sup-', [status(thm)], ['38', '39'])).
% 1.63/1.88  thf('41', plain,
% 1.63/1.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf(cc1_relset_1, axiom,
% 1.63/1.88    (![A:$i,B:$i,C:$i]:
% 1.63/1.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.63/1.88       ( v1_relat_1 @ C ) ))).
% 1.63/1.88  thf('42', plain,
% 1.63/1.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.63/1.88         ((v1_relat_1 @ X7)
% 1.63/1.88          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.63/1.88      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.63/1.88  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 1.63/1.88      inference('sup-', [status(thm)], ['41', '42'])).
% 1.63/1.88  thf('44', plain,
% 1.63/1.88      (![X0 : $i]:
% 1.63/1.88         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 1.63/1.88          | ~ (v1_relat_1 @ X0)
% 1.63/1.88          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ X0)))),
% 1.63/1.88      inference('demod', [status(thm)], ['40', '43'])).
% 1.63/1.88  thf('45', plain,
% 1.63/1.88      ((~ (r1_tarski @ sk_B @ sk_B)
% 1.63/1.88        | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (k2_relat_1 @ sk_E))
% 1.63/1.88        | ~ (v1_relat_1 @ sk_E))),
% 1.63/1.88      inference('sup-', [status(thm)], ['33', '44'])).
% 1.63/1.88  thf(dt_k2_subset_1, axiom,
% 1.63/1.88    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.63/1.88  thf('46', plain,
% 1.63/1.88      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 1.63/1.88      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.63/1.88  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.63/1.88  thf('47', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 1.63/1.88      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.63/1.88  thf('48', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 1.63/1.88      inference('demod', [status(thm)], ['46', '47'])).
% 1.63/1.88  thf(t3_subset, axiom,
% 1.63/1.88    (![A:$i,B:$i]:
% 1.63/1.88     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.63/1.88  thf('49', plain,
% 1.63/1.88      (![X2 : $i, X3 : $i]:
% 1.63/1.88         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 1.63/1.88      inference('cnf', [status(esa)], [t3_subset])).
% 1.63/1.88  thf('50', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.63/1.88      inference('sup-', [status(thm)], ['48', '49'])).
% 1.63/1.88  thf('51', plain,
% 1.63/1.88      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf('52', plain,
% 1.63/1.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.63/1.88         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.63/1.88          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.63/1.88      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.63/1.88  thf('53', plain,
% 1.63/1.88      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 1.63/1.88      inference('sup-', [status(thm)], ['51', '52'])).
% 1.63/1.88  thf('54', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_C))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf('55', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 1.63/1.88      inference('sup+', [status(thm)], ['53', '54'])).
% 1.63/1.88  thf('56', plain,
% 1.63/1.88      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf('57', plain,
% 1.63/1.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.63/1.88         ((v1_relat_1 @ X7)
% 1.63/1.88          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.63/1.88      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.63/1.88  thf('58', plain, ((v1_relat_1 @ sk_E)),
% 1.63/1.88      inference('sup-', [status(thm)], ['56', '57'])).
% 1.63/1.88  thf('59', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.63/1.88      inference('demod', [status(thm)], ['45', '50', '55', '58'])).
% 1.63/1.88  thf('60', plain,
% 1.63/1.88      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.63/1.88      inference('demod', [status(thm)], ['19', '59'])).
% 1.63/1.88  thf('61', plain,
% 1.63/1.88      (((k2_relset_1 @ sk_A @ sk_C @ 
% 1.63/1.88         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) != (sk_C))),
% 1.63/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.88  thf('62', plain,
% 1.63/1.88      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.63/1.88         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.63/1.88      inference('demod', [status(thm)], ['14', '15'])).
% 1.63/1.88  thf('63', plain,
% 1.63/1.88      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 1.63/1.88      inference('demod', [status(thm)], ['61', '62'])).
% 1.63/1.88  thf('64', plain, ($false),
% 1.63/1.88      inference('simplify_reflect-', [status(thm)], ['60', '63'])).
% 1.63/1.88  
% 1.63/1.88  % SZS output end Refutation
% 1.63/1.88  
% 1.63/1.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
