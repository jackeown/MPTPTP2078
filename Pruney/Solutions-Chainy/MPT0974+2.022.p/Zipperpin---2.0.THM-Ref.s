%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tBsGe7xfGb

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:43 EST 2020

% Result     : Theorem 2.58s
% Output     : Refutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 183 expanded)
%              Number of leaves         :   38 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          : 1014 (3569 expanded)
%              Number of equality atoms :   70 ( 261 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X30 ) ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 )
        = ( k5_relat_1 @ X31 @ X34 ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
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

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('34',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('35',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_E )
      = sk_E )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_E )
    = sk_E ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('47',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t199_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( k2_relat_1 @ A )
                  = ( k2_relat_1 @ B ) )
               => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ C ) )
                  = ( k2_relat_1 @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k2_relat_1 @ X5 )
       != ( k2_relat_1 @ X4 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t199_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('50',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['46','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('62',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','62'])).

thf('64',plain,
    ( ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['41','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('67',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['38','39'])).

thf('71',plain,
    ( sk_C
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['64','69','70'])).

thf('72',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['19','71'])).

thf('73',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('75',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tBsGe7xfGb
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:47:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.58/2.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.58/2.75  % Solved by: fo/fo7.sh
% 2.58/2.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.58/2.75  % done 914 iterations in 2.289s
% 2.58/2.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.58/2.75  % SZS output start Refutation
% 2.58/2.75  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.58/2.75  thf(sk_C_type, type, sk_C: $i).
% 2.58/2.75  thf(sk_D_type, type, sk_D: $i).
% 2.58/2.75  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.58/2.75  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.58/2.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.58/2.75  thf(sk_B_type, type, sk_B: $i).
% 2.58/2.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.58/2.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.58/2.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.58/2.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.58/2.75  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.58/2.75  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.58/2.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.58/2.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.58/2.75  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.58/2.75  thf(sk_A_type, type, sk_A: $i).
% 2.58/2.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.58/2.75  thf(sk_E_type, type, sk_E: $i).
% 2.58/2.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.58/2.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.58/2.75  thf(t20_funct_2, conjecture,
% 2.58/2.75    (![A:$i,B:$i,C:$i,D:$i]:
% 2.58/2.75     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.58/2.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.58/2.75       ( ![E:$i]:
% 2.58/2.75         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.58/2.75             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.58/2.75           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.58/2.75               ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 2.58/2.75             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.58/2.75               ( ( k2_relset_1 @
% 2.58/2.75                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.58/2.75                 ( C ) ) ) ) ) ) ))).
% 2.58/2.75  thf(zf_stmt_0, negated_conjecture,
% 2.58/2.75    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.58/2.75        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.58/2.75            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.58/2.75          ( ![E:$i]:
% 2.58/2.75            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.58/2.75                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.58/2.75              ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.58/2.75                  ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 2.58/2.75                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.58/2.75                  ( ( k2_relset_1 @
% 2.58/2.75                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.58/2.75                    ( C ) ) ) ) ) ) ) )),
% 2.58/2.75    inference('cnf.neg', [status(esa)], [t20_funct_2])).
% 2.58/2.75  thf('0', plain,
% 2.58/2.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf('1', plain,
% 2.58/2.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf(dt_k1_partfun1, axiom,
% 2.58/2.75    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.58/2.75     ( ( ( v1_funct_1 @ E ) & 
% 2.58/2.75         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.58/2.75         ( v1_funct_1 @ F ) & 
% 2.58/2.75         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.58/2.75       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.58/2.75         ( m1_subset_1 @
% 2.58/2.75           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.58/2.75           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.58/2.75  thf('2', plain,
% 2.58/2.75      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 2.58/2.75         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.58/2.75          | ~ (v1_funct_1 @ X25)
% 2.58/2.75          | ~ (v1_funct_1 @ X28)
% 2.58/2.75          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.58/2.75          | (m1_subset_1 @ (k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28) @ 
% 2.58/2.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X30))))),
% 2.58/2.75      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.58/2.75  thf('3', plain,
% 2.58/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.58/2.75         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.58/2.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.58/2.75          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.58/2.75          | ~ (v1_funct_1 @ X1)
% 2.58/2.75          | ~ (v1_funct_1 @ sk_D))),
% 2.58/2.75      inference('sup-', [status(thm)], ['1', '2'])).
% 2.58/2.75  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf('5', plain,
% 2.58/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.58/2.75         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.58/2.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.58/2.75          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.58/2.75          | ~ (v1_funct_1 @ X1))),
% 2.58/2.75      inference('demod', [status(thm)], ['3', '4'])).
% 2.58/2.75  thf('6', plain,
% 2.58/2.75      ((~ (v1_funct_1 @ sk_E)
% 2.58/2.75        | (m1_subset_1 @ 
% 2.58/2.75           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 2.58/2.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 2.58/2.75      inference('sup-', [status(thm)], ['0', '5'])).
% 2.58/2.75  thf('7', plain, ((v1_funct_1 @ sk_E)),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf('8', plain,
% 2.58/2.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf('9', plain,
% 2.58/2.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf(redefinition_k1_partfun1, axiom,
% 2.58/2.75    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.58/2.75     ( ( ( v1_funct_1 @ E ) & 
% 2.58/2.75         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.58/2.75         ( v1_funct_1 @ F ) & 
% 2.58/2.75         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.58/2.75       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.58/2.75  thf('10', plain,
% 2.58/2.75      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.58/2.75         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 2.58/2.75          | ~ (v1_funct_1 @ X31)
% 2.58/2.75          | ~ (v1_funct_1 @ X34)
% 2.58/2.75          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 2.58/2.75          | ((k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34)
% 2.58/2.75              = (k5_relat_1 @ X31 @ X34)))),
% 2.58/2.75      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.58/2.75  thf('11', plain,
% 2.58/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.58/2.75         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.58/2.75            = (k5_relat_1 @ sk_D @ X0))
% 2.58/2.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.58/2.75          | ~ (v1_funct_1 @ X0)
% 2.58/2.75          | ~ (v1_funct_1 @ sk_D))),
% 2.58/2.75      inference('sup-', [status(thm)], ['9', '10'])).
% 2.58/2.75  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf('13', plain,
% 2.58/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.58/2.75         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.58/2.75            = (k5_relat_1 @ sk_D @ X0))
% 2.58/2.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.58/2.75          | ~ (v1_funct_1 @ X0))),
% 2.58/2.75      inference('demod', [status(thm)], ['11', '12'])).
% 2.58/2.75  thf('14', plain,
% 2.58/2.75      ((~ (v1_funct_1 @ sk_E)
% 2.58/2.75        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.58/2.75            = (k5_relat_1 @ sk_D @ sk_E)))),
% 2.58/2.75      inference('sup-', [status(thm)], ['8', '13'])).
% 2.58/2.75  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf('16', plain,
% 2.58/2.75      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.58/2.75         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.58/2.75      inference('demod', [status(thm)], ['14', '15'])).
% 2.58/2.75  thf('17', plain,
% 2.58/2.75      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 2.58/2.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.58/2.75      inference('demod', [status(thm)], ['6', '7', '16'])).
% 2.58/2.75  thf(redefinition_k2_relset_1, axiom,
% 2.58/2.75    (![A:$i,B:$i,C:$i]:
% 2.58/2.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.58/2.75       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.58/2.75  thf('18', plain,
% 2.58/2.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.58/2.75         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 2.58/2.75          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.58/2.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.58/2.75  thf('19', plain,
% 2.58/2.75      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 2.58/2.75         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 2.58/2.75      inference('sup-', [status(thm)], ['17', '18'])).
% 2.58/2.75  thf('20', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf(d1_funct_2, axiom,
% 2.58/2.75    (![A:$i,B:$i,C:$i]:
% 2.58/2.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.58/2.75       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.58/2.75           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.58/2.75             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.58/2.75         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.58/2.75           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.58/2.75             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.58/2.75  thf(zf_stmt_1, axiom,
% 2.58/2.75    (![C:$i,B:$i,A:$i]:
% 2.58/2.75     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.58/2.75       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.58/2.75  thf('21', plain,
% 2.58/2.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.58/2.75         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 2.58/2.75          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 2.58/2.75          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.58/2.75  thf('22', plain,
% 2.58/2.75      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 2.58/2.75        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 2.58/2.75      inference('sup-', [status(thm)], ['20', '21'])).
% 2.58/2.75  thf(zf_stmt_2, axiom,
% 2.58/2.75    (![B:$i,A:$i]:
% 2.58/2.75     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.58/2.75       ( zip_tseitin_0 @ B @ A ) ))).
% 2.58/2.75  thf('23', plain,
% 2.58/2.75      (![X17 : $i, X18 : $i]:
% 2.58/2.75         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.58/2.75  thf('24', plain,
% 2.58/2.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.58/2.75  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.58/2.75  thf(zf_stmt_5, axiom,
% 2.58/2.75    (![A:$i,B:$i,C:$i]:
% 2.58/2.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.58/2.75       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.58/2.75         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.58/2.75           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.58/2.75             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.58/2.75  thf('25', plain,
% 2.58/2.75      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.58/2.75         (~ (zip_tseitin_0 @ X22 @ X23)
% 2.58/2.75          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 2.58/2.75          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.58/2.75  thf('26', plain,
% 2.58/2.75      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 2.58/2.75      inference('sup-', [status(thm)], ['24', '25'])).
% 2.58/2.75  thf('27', plain,
% 2.58/2.75      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 2.58/2.75      inference('sup-', [status(thm)], ['23', '26'])).
% 2.58/2.75  thf('28', plain, (((sk_C) != (k1_xboole_0))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf('29', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 2.58/2.75      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 2.58/2.75  thf('30', plain,
% 2.58/2.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf(redefinition_k1_relset_1, axiom,
% 2.58/2.75    (![A:$i,B:$i,C:$i]:
% 2.58/2.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.58/2.75       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.58/2.75  thf('31', plain,
% 2.58/2.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.58/2.75         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 2.58/2.75          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 2.58/2.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.58/2.75  thf('32', plain,
% 2.58/2.75      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 2.58/2.75      inference('sup-', [status(thm)], ['30', '31'])).
% 2.58/2.75  thf('33', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 2.58/2.75      inference('demod', [status(thm)], ['22', '29', '32'])).
% 2.58/2.75  thf(t78_relat_1, axiom,
% 2.58/2.75    (![A:$i]:
% 2.58/2.75     ( ( v1_relat_1 @ A ) =>
% 2.58/2.75       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 2.58/2.75  thf('34', plain,
% 2.58/2.75      (![X9 : $i]:
% 2.58/2.75         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X9)) @ X9) = (X9))
% 2.58/2.75          | ~ (v1_relat_1 @ X9))),
% 2.58/2.75      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.58/2.75  thf('35', plain,
% 2.58/2.75      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_E) = (sk_E))
% 2.58/2.75        | ~ (v1_relat_1 @ sk_E))),
% 2.58/2.75      inference('sup+', [status(thm)], ['33', '34'])).
% 2.58/2.75  thf('36', plain,
% 2.58/2.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf(cc2_relat_1, axiom,
% 2.58/2.75    (![A:$i]:
% 2.58/2.75     ( ( v1_relat_1 @ A ) =>
% 2.58/2.75       ( ![B:$i]:
% 2.58/2.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.58/2.75  thf('37', plain,
% 2.58/2.75      (![X0 : $i, X1 : $i]:
% 2.58/2.75         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.58/2.75          | (v1_relat_1 @ X0)
% 2.58/2.75          | ~ (v1_relat_1 @ X1))),
% 2.58/2.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.58/2.75  thf('38', plain,
% 2.58/2.75      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 2.58/2.75      inference('sup-', [status(thm)], ['36', '37'])).
% 2.58/2.75  thf(fc6_relat_1, axiom,
% 2.58/2.75    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.58/2.75  thf('39', plain,
% 2.58/2.75      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.58/2.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.58/2.75  thf('40', plain, ((v1_relat_1 @ sk_E)),
% 2.58/2.75      inference('demod', [status(thm)], ['38', '39'])).
% 2.58/2.75  thf('41', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_E) = (sk_E))),
% 2.58/2.75      inference('demod', [status(thm)], ['35', '40'])).
% 2.58/2.75  thf('42', plain,
% 2.58/2.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf('43', plain,
% 2.58/2.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.58/2.75         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 2.58/2.75          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.58/2.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.58/2.75  thf('44', plain,
% 2.58/2.75      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.58/2.75      inference('sup-', [status(thm)], ['42', '43'])).
% 2.58/2.75  thf('45', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf('46', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 2.58/2.75      inference('sup+', [status(thm)], ['44', '45'])).
% 2.58/2.75  thf(t71_relat_1, axiom,
% 2.58/2.75    (![A:$i]:
% 2.58/2.75     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.58/2.75       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.58/2.75  thf('47', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 2.58/2.75      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.58/2.75  thf(t199_relat_1, axiom,
% 2.58/2.75    (![A:$i]:
% 2.58/2.75     ( ( v1_relat_1 @ A ) =>
% 2.58/2.75       ( ![B:$i]:
% 2.58/2.75         ( ( v1_relat_1 @ B ) =>
% 2.58/2.75           ( ![C:$i]:
% 2.58/2.75             ( ( v1_relat_1 @ C ) =>
% 2.58/2.75               ( ( ( k2_relat_1 @ A ) = ( k2_relat_1 @ B ) ) =>
% 2.58/2.75                 ( ( k2_relat_1 @ ( k5_relat_1 @ A @ C ) ) =
% 2.58/2.75                   ( k2_relat_1 @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 2.58/2.75  thf('48', plain,
% 2.58/2.75      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.58/2.75         (~ (v1_relat_1 @ X4)
% 2.58/2.75          | ((k2_relat_1 @ X5) != (k2_relat_1 @ X4))
% 2.58/2.75          | ((k2_relat_1 @ (k5_relat_1 @ X5 @ X6))
% 2.58/2.75              = (k2_relat_1 @ (k5_relat_1 @ X4 @ X6)))
% 2.58/2.75          | ~ (v1_relat_1 @ X6)
% 2.58/2.75          | ~ (v1_relat_1 @ X5))),
% 2.58/2.75      inference('cnf', [status(esa)], [t199_relat_1])).
% 2.58/2.75  thf('49', plain,
% 2.58/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.58/2.75         (((X0) != (k2_relat_1 @ X1))
% 2.58/2.75          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.58/2.75          | ~ (v1_relat_1 @ X2)
% 2.58/2.75          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 2.58/2.75              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 2.58/2.75          | ~ (v1_relat_1 @ X1))),
% 2.58/2.75      inference('sup-', [status(thm)], ['47', '48'])).
% 2.58/2.75  thf(t29_relset_1, axiom,
% 2.58/2.75    (![A:$i]:
% 2.58/2.75     ( m1_subset_1 @
% 2.58/2.75       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.58/2.75  thf('50', plain,
% 2.58/2.75      (![X16 : $i]:
% 2.58/2.75         (m1_subset_1 @ (k6_relat_1 @ X16) @ 
% 2.58/2.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))),
% 2.58/2.75      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.58/2.75  thf('51', plain,
% 2.58/2.75      (![X0 : $i, X1 : $i]:
% 2.58/2.75         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.58/2.75          | (v1_relat_1 @ X0)
% 2.58/2.75          | ~ (v1_relat_1 @ X1))),
% 2.58/2.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.58/2.75  thf('52', plain,
% 2.58/2.75      (![X0 : $i]:
% 2.58/2.75         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 2.58/2.75          | (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.58/2.75      inference('sup-', [status(thm)], ['50', '51'])).
% 2.58/2.75  thf('53', plain,
% 2.58/2.75      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.58/2.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.58/2.75  thf('54', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 2.58/2.75      inference('demod', [status(thm)], ['52', '53'])).
% 2.58/2.75  thf('55', plain,
% 2.58/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.58/2.75         (((X0) != (k2_relat_1 @ X1))
% 2.58/2.75          | ~ (v1_relat_1 @ X2)
% 2.58/2.75          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 2.58/2.75              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 2.58/2.75          | ~ (v1_relat_1 @ X1))),
% 2.58/2.75      inference('demod', [status(thm)], ['49', '54'])).
% 2.58/2.75  thf('56', plain,
% 2.58/2.75      (![X1 : $i, X2 : $i]:
% 2.58/2.75         (~ (v1_relat_1 @ X1)
% 2.58/2.75          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X2))
% 2.58/2.75              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 2.58/2.75          | ~ (v1_relat_1 @ X2))),
% 2.58/2.75      inference('simplify', [status(thm)], ['55'])).
% 2.58/2.75  thf('57', plain,
% 2.58/2.75      (![X0 : $i]:
% 2.58/2.75         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0))
% 2.58/2.75            = (k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)))
% 2.58/2.75          | ~ (v1_relat_1 @ X0)
% 2.58/2.75          | ~ (v1_relat_1 @ sk_D))),
% 2.58/2.75      inference('sup+', [status(thm)], ['46', '56'])).
% 2.58/2.75  thf('58', plain,
% 2.58/2.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf('59', plain,
% 2.58/2.75      (![X0 : $i, X1 : $i]:
% 2.58/2.75         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.58/2.75          | (v1_relat_1 @ X0)
% 2.58/2.75          | ~ (v1_relat_1 @ X1))),
% 2.58/2.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.58/2.75  thf('60', plain,
% 2.58/2.75      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 2.58/2.75      inference('sup-', [status(thm)], ['58', '59'])).
% 2.58/2.75  thf('61', plain,
% 2.58/2.75      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.58/2.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.58/2.75  thf('62', plain, ((v1_relat_1 @ sk_D)),
% 2.58/2.75      inference('demod', [status(thm)], ['60', '61'])).
% 2.58/2.75  thf('63', plain,
% 2.58/2.75      (![X0 : $i]:
% 2.58/2.75         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0))
% 2.58/2.75            = (k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)))
% 2.58/2.75          | ~ (v1_relat_1 @ X0))),
% 2.58/2.75      inference('demod', [status(thm)], ['57', '62'])).
% 2.58/2.75  thf('64', plain,
% 2.58/2.75      ((((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 2.58/2.75        | ~ (v1_relat_1 @ sk_E))),
% 2.58/2.75      inference('sup+', [status(thm)], ['41', '63'])).
% 2.58/2.75  thf('65', plain,
% 2.58/2.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf('66', plain,
% 2.58/2.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.58/2.75         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 2.58/2.75          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.58/2.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.58/2.75  thf('67', plain,
% 2.58/2.75      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 2.58/2.75      inference('sup-', [status(thm)], ['65', '66'])).
% 2.58/2.75  thf('68', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_C))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf('69', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 2.58/2.75      inference('sup+', [status(thm)], ['67', '68'])).
% 2.58/2.75  thf('70', plain, ((v1_relat_1 @ sk_E)),
% 2.58/2.75      inference('demod', [status(thm)], ['38', '39'])).
% 2.58/2.75  thf('71', plain, (((sk_C) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 2.58/2.75      inference('demod', [status(thm)], ['64', '69', '70'])).
% 2.58/2.75  thf('72', plain,
% 2.58/2.75      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.58/2.75      inference('demod', [status(thm)], ['19', '71'])).
% 2.58/2.75  thf('73', plain,
% 2.58/2.75      (((k2_relset_1 @ sk_A @ sk_C @ 
% 2.58/2.75         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) != (sk_C))),
% 2.58/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.75  thf('74', plain,
% 2.58/2.75      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.58/2.75         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.58/2.75      inference('demod', [status(thm)], ['14', '15'])).
% 2.58/2.75  thf('75', plain,
% 2.58/2.75      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 2.58/2.75      inference('demod', [status(thm)], ['73', '74'])).
% 2.58/2.75  thf('76', plain, ($false),
% 2.58/2.75      inference('simplify_reflect-', [status(thm)], ['72', '75'])).
% 2.58/2.75  
% 2.58/2.75  % SZS output end Refutation
% 2.58/2.75  
% 2.58/2.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
