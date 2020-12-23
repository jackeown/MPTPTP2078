%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mrHYvJBIcZ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:41 EST 2020

% Result     : Theorem 3.08s
% Output     : Refutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 185 expanded)
%              Number of leaves         :   40 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  979 (3855 expanded)
%              Number of equality atoms :   69 ( 288 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X32 ) ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 )
        = ( k5_relat_1 @ X33 @ X36 ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k8_relset_1 @ X16 @ X17 @ X18 @ X17 )
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('22',plain,
    ( ( k8_relset_1 @ sk_B @ sk_C @ sk_E @ sk_C )
    = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k8_relset_1 @ X13 @ X14 @ X12 @ X15 )
        = ( k10_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_C @ sk_E @ X0 )
      = ( k10_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('28',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('32',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('37',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['22','25','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X3: $i] :
      ( ( ( k10_relat_1 @ X3 @ ( k2_relat_1 @ X3 ) )
        = ( k1_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('44',plain,
    ( ( ( k10_relat_1 @ sk_E @ sk_C )
      = ( k1_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['37','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('55',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) )
        = ( k2_relat_1 @ X5 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ ( k2_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      = ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['49','60'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference('sup+',[status(thm)],['40','41'])).

thf('65',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['45','46'])).

thf('66',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['61','63','64','65'])).

thf('67',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['19','66'])).

thf('68',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('70',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['67','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mrHYvJBIcZ
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.08/3.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.08/3.29  % Solved by: fo/fo7.sh
% 3.08/3.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.08/3.29  % done 997 iterations in 2.840s
% 3.08/3.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.08/3.29  % SZS output start Refutation
% 3.08/3.29  thf(sk_E_type, type, sk_E: $i).
% 3.08/3.29  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.08/3.29  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.08/3.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.08/3.29  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 3.08/3.29  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.08/3.29  thf(sk_A_type, type, sk_A: $i).
% 3.08/3.29  thf(sk_B_type, type, sk_B: $i).
% 3.08/3.29  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.08/3.29  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.08/3.29  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.08/3.29  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.08/3.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.08/3.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.08/3.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.08/3.29  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.08/3.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.08/3.29  thf(sk_C_type, type, sk_C: $i).
% 3.08/3.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.08/3.29  thf(sk_D_type, type, sk_D: $i).
% 3.08/3.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.08/3.29  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 3.08/3.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.08/3.29  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.08/3.29  thf(t20_funct_2, conjecture,
% 3.08/3.29    (![A:$i,B:$i,C:$i,D:$i]:
% 3.08/3.29     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.08/3.29         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.08/3.29       ( ![E:$i]:
% 3.08/3.29         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.08/3.29             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.08/3.29           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 3.08/3.29               ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 3.08/3.29             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 3.08/3.29               ( ( k2_relset_1 @
% 3.08/3.29                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 3.08/3.29                 ( C ) ) ) ) ) ) ))).
% 3.08/3.29  thf(zf_stmt_0, negated_conjecture,
% 3.08/3.29    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.08/3.29        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.08/3.29            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.08/3.29          ( ![E:$i]:
% 3.08/3.29            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.08/3.29                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.08/3.29              ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 3.08/3.29                  ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 3.08/3.29                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 3.08/3.29                  ( ( k2_relset_1 @
% 3.08/3.29                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 3.08/3.29                    ( C ) ) ) ) ) ) ) )),
% 3.08/3.29    inference('cnf.neg', [status(esa)], [t20_funct_2])).
% 3.08/3.29  thf('0', plain,
% 3.08/3.29      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf('1', plain,
% 3.08/3.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf(dt_k1_partfun1, axiom,
% 3.08/3.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.08/3.29     ( ( ( v1_funct_1 @ E ) & 
% 3.08/3.29         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.08/3.29         ( v1_funct_1 @ F ) & 
% 3.08/3.29         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.08/3.29       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.08/3.29         ( m1_subset_1 @
% 3.08/3.29           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.08/3.29           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.08/3.29  thf('2', plain,
% 3.08/3.29      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 3.08/3.29         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.08/3.29          | ~ (v1_funct_1 @ X27)
% 3.08/3.29          | ~ (v1_funct_1 @ X30)
% 3.08/3.29          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.08/3.29          | (m1_subset_1 @ (k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30) @ 
% 3.08/3.29             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X32))))),
% 3.08/3.29      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.08/3.29  thf('3', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.08/3.29         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 3.08/3.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.08/3.29          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.08/3.29          | ~ (v1_funct_1 @ X1)
% 3.08/3.29          | ~ (v1_funct_1 @ sk_D))),
% 3.08/3.29      inference('sup-', [status(thm)], ['1', '2'])).
% 3.08/3.29  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf('5', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.08/3.29         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 3.08/3.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.08/3.29          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.08/3.29          | ~ (v1_funct_1 @ X1))),
% 3.08/3.29      inference('demod', [status(thm)], ['3', '4'])).
% 3.08/3.29  thf('6', plain,
% 3.08/3.29      ((~ (v1_funct_1 @ sk_E)
% 3.08/3.29        | (m1_subset_1 @ 
% 3.08/3.29           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 3.08/3.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 3.08/3.29      inference('sup-', [status(thm)], ['0', '5'])).
% 3.08/3.29  thf('7', plain, ((v1_funct_1 @ sk_E)),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf('8', plain,
% 3.08/3.29      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf('9', plain,
% 3.08/3.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf(redefinition_k1_partfun1, axiom,
% 3.08/3.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.08/3.29     ( ( ( v1_funct_1 @ E ) & 
% 3.08/3.29         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.08/3.29         ( v1_funct_1 @ F ) & 
% 3.08/3.29         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.08/3.29       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.08/3.29  thf('10', plain,
% 3.08/3.29      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.08/3.29         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.08/3.29          | ~ (v1_funct_1 @ X33)
% 3.08/3.29          | ~ (v1_funct_1 @ X36)
% 3.08/3.29          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 3.08/3.29          | ((k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)
% 3.08/3.29              = (k5_relat_1 @ X33 @ X36)))),
% 3.08/3.29      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.08/3.29  thf('11', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.08/3.29         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 3.08/3.29            = (k5_relat_1 @ sk_D @ X0))
% 3.08/3.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.08/3.29          | ~ (v1_funct_1 @ X0)
% 3.08/3.29          | ~ (v1_funct_1 @ sk_D))),
% 3.08/3.29      inference('sup-', [status(thm)], ['9', '10'])).
% 3.08/3.29  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf('13', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.08/3.29         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 3.08/3.29            = (k5_relat_1 @ sk_D @ X0))
% 3.08/3.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.08/3.29          | ~ (v1_funct_1 @ X0))),
% 3.08/3.29      inference('demod', [status(thm)], ['11', '12'])).
% 3.08/3.29  thf('14', plain,
% 3.08/3.29      ((~ (v1_funct_1 @ sk_E)
% 3.08/3.29        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 3.08/3.29            = (k5_relat_1 @ sk_D @ sk_E)))),
% 3.08/3.29      inference('sup-', [status(thm)], ['8', '13'])).
% 3.08/3.29  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf('16', plain,
% 3.08/3.29      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 3.08/3.29         = (k5_relat_1 @ sk_D @ sk_E))),
% 3.08/3.29      inference('demod', [status(thm)], ['14', '15'])).
% 3.08/3.29  thf('17', plain,
% 3.08/3.29      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 3.08/3.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 3.08/3.29      inference('demod', [status(thm)], ['6', '7', '16'])).
% 3.08/3.29  thf(redefinition_k2_relset_1, axiom,
% 3.08/3.29    (![A:$i,B:$i,C:$i]:
% 3.08/3.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.08/3.29       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.08/3.29  thf('18', plain,
% 3.08/3.29      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.08/3.29         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 3.08/3.29          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 3.08/3.29      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.08/3.29  thf('19', plain,
% 3.08/3.29      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 3.08/3.29         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 3.08/3.29      inference('sup-', [status(thm)], ['17', '18'])).
% 3.08/3.29  thf('20', plain,
% 3.08/3.29      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf(t38_relset_1, axiom,
% 3.08/3.29    (![A:$i,B:$i,C:$i]:
% 3.08/3.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.08/3.29       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 3.08/3.29         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.08/3.29  thf('21', plain,
% 3.08/3.29      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.08/3.29         (((k8_relset_1 @ X16 @ X17 @ X18 @ X17)
% 3.08/3.29            = (k1_relset_1 @ X16 @ X17 @ X18))
% 3.08/3.29          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.08/3.29      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.08/3.29  thf('22', plain,
% 3.08/3.29      (((k8_relset_1 @ sk_B @ sk_C @ sk_E @ sk_C)
% 3.08/3.29         = (k1_relset_1 @ sk_B @ sk_C @ sk_E))),
% 3.08/3.29      inference('sup-', [status(thm)], ['20', '21'])).
% 3.08/3.29  thf('23', plain,
% 3.08/3.29      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf(redefinition_k8_relset_1, axiom,
% 3.08/3.29    (![A:$i,B:$i,C:$i,D:$i]:
% 3.08/3.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.08/3.29       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 3.08/3.29  thf('24', plain,
% 3.08/3.29      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.08/3.29         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 3.08/3.29          | ((k8_relset_1 @ X13 @ X14 @ X12 @ X15) = (k10_relat_1 @ X12 @ X15)))),
% 3.08/3.29      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.08/3.29  thf('25', plain,
% 3.08/3.29      (![X0 : $i]:
% 3.08/3.29         ((k8_relset_1 @ sk_B @ sk_C @ sk_E @ X0) = (k10_relat_1 @ sk_E @ X0))),
% 3.08/3.29      inference('sup-', [status(thm)], ['23', '24'])).
% 3.08/3.29  thf('26', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf(d1_funct_2, axiom,
% 3.08/3.29    (![A:$i,B:$i,C:$i]:
% 3.08/3.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.08/3.29       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.08/3.29           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.08/3.29             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.08/3.29         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.08/3.29           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.08/3.29             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.08/3.29  thf(zf_stmt_1, axiom,
% 3.08/3.29    (![C:$i,B:$i,A:$i]:
% 3.08/3.29     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.08/3.29       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.08/3.29  thf('27', plain,
% 3.08/3.29      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.08/3.29         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 3.08/3.29          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 3.08/3.29          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.08/3.29  thf('28', plain,
% 3.08/3.29      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 3.08/3.29        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 3.08/3.29      inference('sup-', [status(thm)], ['26', '27'])).
% 3.08/3.29  thf(zf_stmt_2, axiom,
% 3.08/3.29    (![B:$i,A:$i]:
% 3.08/3.29     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.08/3.29       ( zip_tseitin_0 @ B @ A ) ))).
% 3.08/3.29  thf('29', plain,
% 3.08/3.29      (![X19 : $i, X20 : $i]:
% 3.08/3.29         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.08/3.29  thf('30', plain,
% 3.08/3.29      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.08/3.29  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.08/3.29  thf(zf_stmt_5, axiom,
% 3.08/3.29    (![A:$i,B:$i,C:$i]:
% 3.08/3.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.08/3.29       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.08/3.29         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.08/3.29           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.08/3.29             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.08/3.29  thf('31', plain,
% 3.08/3.29      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.08/3.29         (~ (zip_tseitin_0 @ X24 @ X25)
% 3.08/3.29          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 3.08/3.29          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.08/3.29  thf('32', plain,
% 3.08/3.29      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 3.08/3.29      inference('sup-', [status(thm)], ['30', '31'])).
% 3.08/3.29  thf('33', plain,
% 3.08/3.29      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 3.08/3.29      inference('sup-', [status(thm)], ['29', '32'])).
% 3.08/3.29  thf('34', plain, (((sk_C) != (k1_xboole_0))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf('35', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 3.08/3.29      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 3.08/3.29  thf('36', plain, (((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E))),
% 3.08/3.29      inference('demod', [status(thm)], ['28', '35'])).
% 3.08/3.29  thf('37', plain, (((k10_relat_1 @ sk_E @ sk_C) = (sk_B))),
% 3.08/3.29      inference('demod', [status(thm)], ['22', '25', '36'])).
% 3.08/3.29  thf('38', plain,
% 3.08/3.29      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf('39', plain,
% 3.08/3.29      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.08/3.29         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 3.08/3.29          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 3.08/3.29      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.08/3.29  thf('40', plain,
% 3.08/3.29      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 3.08/3.29      inference('sup-', [status(thm)], ['38', '39'])).
% 3.08/3.29  thf('41', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_C))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf('42', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 3.08/3.29      inference('sup+', [status(thm)], ['40', '41'])).
% 3.08/3.29  thf(t169_relat_1, axiom,
% 3.08/3.29    (![A:$i]:
% 3.08/3.29     ( ( v1_relat_1 @ A ) =>
% 3.08/3.29       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 3.08/3.29  thf('43', plain,
% 3.08/3.29      (![X3 : $i]:
% 3.08/3.29         (((k10_relat_1 @ X3 @ (k2_relat_1 @ X3)) = (k1_relat_1 @ X3))
% 3.08/3.29          | ~ (v1_relat_1 @ X3))),
% 3.08/3.29      inference('cnf', [status(esa)], [t169_relat_1])).
% 3.08/3.29  thf('44', plain,
% 3.08/3.29      ((((k10_relat_1 @ sk_E @ sk_C) = (k1_relat_1 @ sk_E))
% 3.08/3.29        | ~ (v1_relat_1 @ sk_E))),
% 3.08/3.29      inference('sup+', [status(thm)], ['42', '43'])).
% 3.08/3.29  thf('45', plain,
% 3.08/3.29      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf(cc1_relset_1, axiom,
% 3.08/3.29    (![A:$i,B:$i,C:$i]:
% 3.08/3.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.08/3.29       ( v1_relat_1 @ C ) ))).
% 3.08/3.29  thf('46', plain,
% 3.08/3.29      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.08/3.29         ((v1_relat_1 @ X6)
% 3.08/3.29          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 3.08/3.29      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.08/3.29  thf('47', plain, ((v1_relat_1 @ sk_E)),
% 3.08/3.29      inference('sup-', [status(thm)], ['45', '46'])).
% 3.08/3.29  thf('48', plain, (((k10_relat_1 @ sk_E @ sk_C) = (k1_relat_1 @ sk_E))),
% 3.08/3.29      inference('demod', [status(thm)], ['44', '47'])).
% 3.08/3.29  thf('49', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 3.08/3.29      inference('sup+', [status(thm)], ['37', '48'])).
% 3.08/3.29  thf('50', plain,
% 3.08/3.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf('51', plain,
% 3.08/3.29      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.08/3.29         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 3.08/3.29          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 3.08/3.29      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.08/3.29  thf('52', plain,
% 3.08/3.29      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.08/3.29      inference('sup-', [status(thm)], ['50', '51'])).
% 3.08/3.29  thf('53', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf('54', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 3.08/3.29      inference('sup+', [status(thm)], ['52', '53'])).
% 3.08/3.29  thf(t47_relat_1, axiom,
% 3.08/3.29    (![A:$i]:
% 3.08/3.29     ( ( v1_relat_1 @ A ) =>
% 3.08/3.29       ( ![B:$i]:
% 3.08/3.29         ( ( v1_relat_1 @ B ) =>
% 3.08/3.29           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 3.08/3.29             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 3.08/3.29  thf('55', plain,
% 3.08/3.29      (![X4 : $i, X5 : $i]:
% 3.08/3.29         (~ (v1_relat_1 @ X4)
% 3.08/3.29          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ X5)) = (k2_relat_1 @ X5))
% 3.08/3.29          | ~ (r1_tarski @ (k1_relat_1 @ X5) @ (k2_relat_1 @ X4))
% 3.08/3.29          | ~ (v1_relat_1 @ X5))),
% 3.08/3.29      inference('cnf', [status(esa)], [t47_relat_1])).
% 3.08/3.29  thf('56', plain,
% 3.08/3.29      (![X0 : $i]:
% 3.08/3.29         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 3.08/3.29          | ~ (v1_relat_1 @ X0)
% 3.08/3.29          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ X0))
% 3.08/3.29          | ~ (v1_relat_1 @ sk_D))),
% 3.08/3.29      inference('sup-', [status(thm)], ['54', '55'])).
% 3.08/3.29  thf('57', plain,
% 3.08/3.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf('58', plain,
% 3.08/3.29      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.08/3.29         ((v1_relat_1 @ X6)
% 3.08/3.29          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 3.08/3.29      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.08/3.29  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 3.08/3.29      inference('sup-', [status(thm)], ['57', '58'])).
% 3.08/3.29  thf('60', plain,
% 3.08/3.29      (![X0 : $i]:
% 3.08/3.29         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 3.08/3.29          | ~ (v1_relat_1 @ X0)
% 3.08/3.29          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ X0)))),
% 3.08/3.29      inference('demod', [status(thm)], ['56', '59'])).
% 3.08/3.29  thf('61', plain,
% 3.08/3.29      ((~ (r1_tarski @ sk_B @ sk_B)
% 3.08/3.29        | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (k2_relat_1 @ sk_E))
% 3.08/3.29        | ~ (v1_relat_1 @ sk_E))),
% 3.08/3.29      inference('sup-', [status(thm)], ['49', '60'])).
% 3.08/3.29  thf(d10_xboole_0, axiom,
% 3.08/3.29    (![A:$i,B:$i]:
% 3.08/3.29     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.08/3.29  thf('62', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.08/3.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.08/3.29  thf('63', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.08/3.29      inference('simplify', [status(thm)], ['62'])).
% 3.08/3.29  thf('64', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 3.08/3.29      inference('sup+', [status(thm)], ['40', '41'])).
% 3.08/3.29  thf('65', plain, ((v1_relat_1 @ sk_E)),
% 3.08/3.29      inference('sup-', [status(thm)], ['45', '46'])).
% 3.08/3.29  thf('66', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 3.08/3.29      inference('demod', [status(thm)], ['61', '63', '64', '65'])).
% 3.08/3.29  thf('67', plain,
% 3.08/3.29      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 3.08/3.29      inference('demod', [status(thm)], ['19', '66'])).
% 3.08/3.29  thf('68', plain,
% 3.08/3.29      (((k2_relset_1 @ sk_A @ sk_C @ 
% 3.08/3.29         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) != (sk_C))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf('69', plain,
% 3.08/3.29      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 3.08/3.29         = (k5_relat_1 @ sk_D @ sk_E))),
% 3.08/3.29      inference('demod', [status(thm)], ['14', '15'])).
% 3.08/3.29  thf('70', plain,
% 3.08/3.29      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 3.08/3.29      inference('demod', [status(thm)], ['68', '69'])).
% 3.08/3.29  thf('71', plain, ($false),
% 3.08/3.29      inference('simplify_reflect-', [status(thm)], ['67', '70'])).
% 3.08/3.29  
% 3.08/3.29  % SZS output end Refutation
% 3.08/3.29  
% 3.08/3.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
