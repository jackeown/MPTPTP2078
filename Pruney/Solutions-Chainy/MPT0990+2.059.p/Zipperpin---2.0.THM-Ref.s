%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rXT1nJKX3k

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:03 EST 2020

% Result     : Theorem 10.65s
% Output     : Refutation 10.65s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 294 expanded)
%              Number of leaves         :   39 ( 104 expanded)
%              Depth                    :   14
%              Number of atoms          : 1550 (8417 expanded)
%              Number of equality atoms :   83 ( 572 expanded)
%              Maximal formula depth    :   26 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('5',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22 )
        = ( k5_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_D_1 )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      = ( k5_relat_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1 )
    = ( k5_relat_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
        <=> ! [D: $i] :
              ( ( D != k1_xboole_0 )
             => ! [E: $i] :
                  ( ( ( v1_funct_1 @ E )
                    & ( v1_funct_2 @ E @ B @ D )
                    & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) )
                 => ! [F: $i] :
                      ( ( ( v1_funct_1 @ F )
                        & ( v1_funct_2 @ F @ B @ D )
                        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) )
                     => ( ( r2_relset_1 @ A @ D @ ( k1_partfun1 @ A @ B @ B @ D @ C @ E ) @ ( k1_partfun1 @ A @ B @ B @ D @ C @ F ) )
                       => ( r2_relset_1 @ B @ D @ E @ F ) ) ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ( X29 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X26 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X29 ) ) )
      | ( r2_relset_1 @ X26 @ X29 @ X31 @ X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ ( k1_partfun1 @ X28 @ X26 @ X26 @ X29 @ X27 @ X31 ) @ ( k1_partfun1 @ X28 @ X26 @ X26 @ X29 @ X27 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X26 @ X29 )
      | ~ ( v1_funct_1 @ X31 )
      | ( ( k2_relset_1 @ X28 @ X26 @ X27 )
       != X26 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_2])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
       != sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ~ ( r2_relset_1 @ sk_A @ X1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0 ) @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2 ) )
      | ( r2_relset_1 @ sk_B @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ sk_B @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_B != sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ~ ( r2_relset_1 @ sk_A @ X1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0 ) @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2 ) )
      | ( r2_relset_1 @ sk_B @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ sk_B @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( X1 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ( r2_relset_1 @ sk_B @ X1 @ X0 @ X2 )
      | ~ ( r2_relset_1 @ sk_A @ X1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0 ) @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ( r2_relset_1 @ sk_B @ X1 @ X0 @ X2 )
      | ~ ( r2_relset_1 @ sk_A @ X1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0 ) @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D_1 ) @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D_1 ) @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ( r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D_1 ) @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ( r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D_1 ) @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','49'])).

thf('51',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['25'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X32 ) @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('62',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D_1 ) @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ( r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','60','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('64',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('65',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( X7 = X10 )
      | ~ ( r2_relset_1 @ X8 @ X9 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ X0 )
      | ( sk_D_1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_D_1
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    sk_D_1
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ~ ( r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D_1 ) @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['62','69'])).

thf('71',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D_1 ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','70'])).

thf('72',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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

thf('73',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ( X13
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('74',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('75',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('78',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('83',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_relset_1 @ X5 @ X6 @ X4 )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('84',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['74','81','84'])).

thf('86',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1 )
    = ( k5_relat_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('88',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('90',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['71','85','88','91','92','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rXT1nJKX3k
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 10.65/10.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.65/10.83  % Solved by: fo/fo7.sh
% 10.65/10.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.65/10.83  % done 1411 iterations in 10.381s
% 10.65/10.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.65/10.83  % SZS output start Refutation
% 10.65/10.83  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 10.65/10.83  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 10.65/10.83  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 10.65/10.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 10.65/10.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 10.65/10.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 10.65/10.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 10.65/10.83  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 10.65/10.83  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 10.65/10.83  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 10.65/10.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.65/10.83  thf(sk_D_1_type, type, sk_D_1: $i).
% 10.65/10.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 10.65/10.83  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 10.65/10.83  thf(sk_C_type, type, sk_C: $i).
% 10.65/10.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.65/10.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.65/10.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.65/10.83  thf(sk_B_type, type, sk_B: $i).
% 10.65/10.83  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 10.65/10.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.65/10.83  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 10.65/10.83  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 10.65/10.83  thf(sk_A_type, type, sk_A: $i).
% 10.65/10.83  thf(t61_funct_1, axiom,
% 10.65/10.83    (![A:$i]:
% 10.65/10.83     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 10.65/10.83       ( ( v2_funct_1 @ A ) =>
% 10.65/10.83         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 10.65/10.83             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 10.65/10.83           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 10.65/10.83             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 10.65/10.83  thf('0', plain,
% 10.65/10.83      (![X0 : $i]:
% 10.65/10.83         (~ (v2_funct_1 @ X0)
% 10.65/10.83          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 10.65/10.83              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 10.65/10.83          | ~ (v1_funct_1 @ X0)
% 10.65/10.83          | ~ (v1_relat_1 @ X0))),
% 10.65/10.83      inference('cnf', [status(esa)], [t61_funct_1])).
% 10.65/10.83  thf(redefinition_k6_partfun1, axiom,
% 10.65/10.83    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 10.65/10.83  thf('1', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 10.65/10.83      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.65/10.83  thf('2', plain,
% 10.65/10.83      (![X0 : $i]:
% 10.65/10.83         (~ (v2_funct_1 @ X0)
% 10.65/10.83          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 10.65/10.83              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 10.65/10.83          | ~ (v1_funct_1 @ X0)
% 10.65/10.83          | ~ (v1_relat_1 @ X0))),
% 10.65/10.83      inference('demod', [status(thm)], ['0', '1'])).
% 10.65/10.83  thf(t36_funct_2, conjecture,
% 10.65/10.83    (![A:$i,B:$i,C:$i]:
% 10.65/10.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.65/10.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.65/10.83       ( ![D:$i]:
% 10.65/10.83         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 10.65/10.83             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 10.65/10.83           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 10.65/10.83               ( r2_relset_1 @
% 10.65/10.83                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 10.65/10.83                 ( k6_partfun1 @ A ) ) & 
% 10.65/10.83               ( v2_funct_1 @ C ) ) =>
% 10.65/10.83             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 10.65/10.83               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 10.65/10.83  thf(zf_stmt_0, negated_conjecture,
% 10.65/10.83    (~( ![A:$i,B:$i,C:$i]:
% 10.65/10.83        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.65/10.83            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.65/10.83          ( ![D:$i]:
% 10.65/10.83            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 10.65/10.83                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 10.65/10.83              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 10.65/10.83                  ( r2_relset_1 @
% 10.65/10.83                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 10.65/10.83                    ( k6_partfun1 @ A ) ) & 
% 10.65/10.83                  ( v2_funct_1 @ C ) ) =>
% 10.65/10.83                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 10.65/10.83                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 10.65/10.83    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 10.65/10.83  thf('3', plain,
% 10.65/10.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf(t31_funct_2, axiom,
% 10.65/10.83    (![A:$i,B:$i,C:$i]:
% 10.65/10.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.65/10.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.65/10.83       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 10.65/10.83         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 10.65/10.83           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 10.65/10.83           ( m1_subset_1 @
% 10.65/10.83             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 10.65/10.83  thf('4', plain,
% 10.65/10.83      (![X32 : $i, X33 : $i, X34 : $i]:
% 10.65/10.83         (~ (v2_funct_1 @ X32)
% 10.65/10.83          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 10.65/10.83          | (m1_subset_1 @ (k2_funct_1 @ X32) @ 
% 10.65/10.83             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 10.65/10.83          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 10.65/10.83          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 10.65/10.83          | ~ (v1_funct_1 @ X32))),
% 10.65/10.83      inference('cnf', [status(esa)], [t31_funct_2])).
% 10.65/10.83  thf('5', plain,
% 10.65/10.83      ((~ (v1_funct_1 @ sk_C)
% 10.65/10.83        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 10.65/10.83        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 10.65/10.83           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 10.65/10.83        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 10.65/10.83        | ~ (v2_funct_1 @ sk_C))),
% 10.65/10.83      inference('sup-', [status(thm)], ['3', '4'])).
% 10.65/10.83  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('7', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('9', plain, ((v2_funct_1 @ sk_C)),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('10', plain,
% 10.65/10.83      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 10.65/10.83         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 10.65/10.83        | ((sk_B) != (sk_B)))),
% 10.65/10.83      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 10.65/10.83  thf('11', plain,
% 10.65/10.83      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 10.65/10.83        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 10.65/10.83      inference('simplify', [status(thm)], ['10'])).
% 10.65/10.83  thf('12', plain,
% 10.65/10.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf(redefinition_k1_partfun1, axiom,
% 10.65/10.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.65/10.83     ( ( ( v1_funct_1 @ E ) & 
% 10.65/10.83         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.65/10.83         ( v1_funct_1 @ F ) & 
% 10.65/10.83         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 10.65/10.83       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 10.65/10.83  thf('13', plain,
% 10.65/10.83      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 10.65/10.83         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 10.65/10.83          | ~ (v1_funct_1 @ X19)
% 10.65/10.83          | ~ (v1_funct_1 @ X22)
% 10.65/10.83          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 10.65/10.83          | ((k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22)
% 10.65/10.83              = (k5_relat_1 @ X19 @ X22)))),
% 10.65/10.83      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 10.65/10.83  thf('14', plain,
% 10.65/10.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.65/10.83         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 10.65/10.83            = (k5_relat_1 @ sk_C @ X0))
% 10.65/10.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.65/10.83          | ~ (v1_funct_1 @ X0)
% 10.65/10.83          | ~ (v1_funct_1 @ sk_C))),
% 10.65/10.83      inference('sup-', [status(thm)], ['12', '13'])).
% 10.65/10.83  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('16', plain,
% 10.65/10.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.65/10.83         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 10.65/10.83            = (k5_relat_1 @ sk_C @ X0))
% 10.65/10.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.65/10.83          | ~ (v1_funct_1 @ X0))),
% 10.65/10.83      inference('demod', [status(thm)], ['14', '15'])).
% 10.65/10.83  thf('17', plain,
% 10.65/10.83      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 10.65/10.83        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 10.65/10.83            (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 10.65/10.83      inference('sup-', [status(thm)], ['11', '16'])).
% 10.65/10.83  thf('18', plain,
% 10.65/10.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('19', plain,
% 10.65/10.83      (![X32 : $i, X33 : $i, X34 : $i]:
% 10.65/10.83         (~ (v2_funct_1 @ X32)
% 10.65/10.83          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 10.65/10.83          | (v1_funct_1 @ (k2_funct_1 @ X32))
% 10.65/10.83          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 10.65/10.83          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 10.65/10.83          | ~ (v1_funct_1 @ X32))),
% 10.65/10.83      inference('cnf', [status(esa)], [t31_funct_2])).
% 10.65/10.83  thf('20', plain,
% 10.65/10.83      ((~ (v1_funct_1 @ sk_C)
% 10.65/10.83        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 10.65/10.83        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 10.65/10.83        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 10.65/10.83        | ~ (v2_funct_1 @ sk_C))),
% 10.65/10.83      inference('sup-', [status(thm)], ['18', '19'])).
% 10.65/10.83  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('22', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('23', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('24', plain, ((v2_funct_1 @ sk_C)),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('25', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)) | ((sk_B) != (sk_B)))),
% 10.65/10.83      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 10.65/10.83  thf('26', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 10.65/10.83      inference('simplify', [status(thm)], ['25'])).
% 10.65/10.83  thf('27', plain,
% 10.65/10.83      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 10.65/10.83         = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 10.65/10.83      inference('demod', [status(thm)], ['17', '26'])).
% 10.65/10.83  thf('28', plain,
% 10.65/10.83      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('29', plain,
% 10.65/10.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.65/10.83         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 10.65/10.83            = (k5_relat_1 @ sk_C @ X0))
% 10.65/10.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.65/10.83          | ~ (v1_funct_1 @ X0))),
% 10.65/10.83      inference('demod', [status(thm)], ['14', '15'])).
% 10.65/10.83  thf('30', plain,
% 10.65/10.83      ((~ (v1_funct_1 @ sk_D_1)
% 10.65/10.83        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 10.65/10.83            = (k5_relat_1 @ sk_C @ sk_D_1)))),
% 10.65/10.83      inference('sup-', [status(thm)], ['28', '29'])).
% 10.65/10.83  thf('31', plain, ((v1_funct_1 @ sk_D_1)),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('32', plain,
% 10.65/10.83      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 10.65/10.83         = (k5_relat_1 @ sk_C @ sk_D_1))),
% 10.65/10.83      inference('demod', [status(thm)], ['30', '31'])).
% 10.65/10.83  thf('33', plain,
% 10.65/10.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf(t22_funct_2, axiom,
% 10.65/10.83    (![A:$i,B:$i,C:$i]:
% 10.65/10.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.65/10.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.65/10.83       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 10.65/10.83         ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) <=>
% 10.65/10.83           ( ![D:$i]:
% 10.65/10.83             ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 10.65/10.83               ( ![E:$i]:
% 10.65/10.83                 ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ D ) & 
% 10.65/10.83                     ( m1_subset_1 @
% 10.65/10.83                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) =>
% 10.65/10.83                   ( ![F:$i]:
% 10.65/10.83                     ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ B @ D ) & 
% 10.65/10.83                         ( m1_subset_1 @
% 10.65/10.83                           F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) =>
% 10.65/10.83                       ( ( r2_relset_1 @
% 10.65/10.83                           A @ D @ ( k1_partfun1 @ A @ B @ B @ D @ C @ E ) @ 
% 10.65/10.83                           ( k1_partfun1 @ A @ B @ B @ D @ C @ F ) ) =>
% 10.65/10.83                         ( r2_relset_1 @ B @ D @ E @ F ) ) ) ) ) ) ) ) ) ) ))).
% 10.65/10.83  thf('34', plain,
% 10.65/10.83      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 10.65/10.83         (((X26) = (k1_xboole_0))
% 10.65/10.83          | ~ (v1_funct_1 @ X27)
% 10.65/10.83          | ~ (v1_funct_2 @ X27 @ X28 @ X26)
% 10.65/10.83          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 10.65/10.83          | ((X29) = (k1_xboole_0))
% 10.65/10.83          | ~ (v1_funct_1 @ X30)
% 10.65/10.83          | ~ (v1_funct_2 @ X30 @ X26 @ X29)
% 10.65/10.83          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X29)))
% 10.65/10.83          | (r2_relset_1 @ X26 @ X29 @ X31 @ X30)
% 10.65/10.83          | ~ (r2_relset_1 @ X28 @ X29 @ 
% 10.65/10.83               (k1_partfun1 @ X28 @ X26 @ X26 @ X29 @ X27 @ X31) @ 
% 10.65/10.83               (k1_partfun1 @ X28 @ X26 @ X26 @ X29 @ X27 @ X30))
% 10.65/10.83          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X29)))
% 10.65/10.83          | ~ (v1_funct_2 @ X31 @ X26 @ X29)
% 10.65/10.83          | ~ (v1_funct_1 @ X31)
% 10.65/10.83          | ((k2_relset_1 @ X28 @ X26 @ X27) != (X26)))),
% 10.65/10.83      inference('cnf', [status(esa)], [t22_funct_2])).
% 10.65/10.83  thf('35', plain,
% 10.65/10.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.65/10.83         (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 10.65/10.83          | ~ (v1_funct_1 @ X0)
% 10.65/10.83          | ~ (v1_funct_2 @ X0 @ sk_B @ X1)
% 10.65/10.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 10.65/10.83          | ~ (r2_relset_1 @ sk_A @ X1 @ 
% 10.65/10.83               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0) @ 
% 10.65/10.83               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2))
% 10.65/10.83          | (r2_relset_1 @ sk_B @ X1 @ X0 @ X2)
% 10.65/10.83          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 10.65/10.83          | ~ (v1_funct_2 @ X2 @ sk_B @ X1)
% 10.65/10.83          | ~ (v1_funct_1 @ X2)
% 10.65/10.83          | ((X1) = (k1_xboole_0))
% 10.65/10.83          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 10.65/10.83          | ~ (v1_funct_1 @ sk_C)
% 10.65/10.83          | ((sk_B) = (k1_xboole_0)))),
% 10.65/10.83      inference('sup-', [status(thm)], ['33', '34'])).
% 10.65/10.83  thf('36', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('37', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('39', plain,
% 10.65/10.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.65/10.83         (((sk_B) != (sk_B))
% 10.65/10.83          | ~ (v1_funct_1 @ X0)
% 10.65/10.83          | ~ (v1_funct_2 @ X0 @ sk_B @ X1)
% 10.65/10.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 10.65/10.83          | ~ (r2_relset_1 @ sk_A @ X1 @ 
% 10.65/10.83               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0) @ 
% 10.65/10.83               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2))
% 10.65/10.83          | (r2_relset_1 @ sk_B @ X1 @ X0 @ X2)
% 10.65/10.83          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 10.65/10.83          | ~ (v1_funct_2 @ X2 @ sk_B @ X1)
% 10.65/10.83          | ~ (v1_funct_1 @ X2)
% 10.65/10.83          | ((X1) = (k1_xboole_0))
% 10.65/10.83          | ((sk_B) = (k1_xboole_0)))),
% 10.65/10.83      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 10.65/10.83  thf('40', plain,
% 10.65/10.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.65/10.83         (((sk_B) = (k1_xboole_0))
% 10.65/10.83          | ((X1) = (k1_xboole_0))
% 10.65/10.83          | ~ (v1_funct_1 @ X2)
% 10.65/10.83          | ~ (v1_funct_2 @ X2 @ sk_B @ X1)
% 10.65/10.83          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 10.65/10.83          | (r2_relset_1 @ sk_B @ X1 @ X0 @ X2)
% 10.65/10.83          | ~ (r2_relset_1 @ sk_A @ X1 @ 
% 10.65/10.83               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0) @ 
% 10.65/10.83               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2))
% 10.65/10.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 10.65/10.83          | ~ (v1_funct_2 @ X0 @ sk_B @ X1)
% 10.65/10.83          | ~ (v1_funct_1 @ X0))),
% 10.65/10.83      inference('simplify', [status(thm)], ['39'])).
% 10.65/10.83  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('42', plain,
% 10.65/10.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.65/10.83         (((X1) = (k1_xboole_0))
% 10.65/10.83          | ~ (v1_funct_1 @ X2)
% 10.65/10.83          | ~ (v1_funct_2 @ X2 @ sk_B @ X1)
% 10.65/10.83          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 10.65/10.83          | (r2_relset_1 @ sk_B @ X1 @ X0 @ X2)
% 10.65/10.83          | ~ (r2_relset_1 @ sk_A @ X1 @ 
% 10.65/10.83               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0) @ 
% 10.65/10.83               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2))
% 10.65/10.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 10.65/10.83          | ~ (v1_funct_2 @ X0 @ sk_B @ X1)
% 10.65/10.83          | ~ (v1_funct_1 @ X0))),
% 10.65/10.83      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 10.65/10.83  thf('43', plain,
% 10.65/10.83      (![X0 : $i]:
% 10.65/10.83         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 10.65/10.83             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0))
% 10.65/10.83          | ~ (v1_funct_1 @ sk_D_1)
% 10.65/10.83          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_A)
% 10.65/10.83          | ~ (m1_subset_1 @ sk_D_1 @ 
% 10.65/10.83               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 10.65/10.83          | (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ X0)
% 10.65/10.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 10.65/10.83          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 10.65/10.83          | ~ (v1_funct_1 @ X0)
% 10.65/10.83          | ((sk_A) = (k1_xboole_0)))),
% 10.65/10.83      inference('sup-', [status(thm)], ['32', '42'])).
% 10.65/10.83  thf('44', plain, ((v1_funct_1 @ sk_D_1)),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('45', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_A)),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('46', plain,
% 10.65/10.83      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('47', plain,
% 10.65/10.83      (![X0 : $i]:
% 10.65/10.83         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 10.65/10.83             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0))
% 10.65/10.83          | (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ X0)
% 10.65/10.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 10.65/10.83          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 10.65/10.83          | ~ (v1_funct_1 @ X0)
% 10.65/10.83          | ((sk_A) = (k1_xboole_0)))),
% 10.65/10.83      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 10.65/10.83  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('49', plain,
% 10.65/10.83      (![X0 : $i]:
% 10.65/10.83         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 10.65/10.83             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0))
% 10.65/10.83          | (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ X0)
% 10.65/10.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 10.65/10.83          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 10.65/10.83          | ~ (v1_funct_1 @ X0))),
% 10.65/10.83      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 10.65/10.83  thf('50', plain,
% 10.65/10.83      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 10.65/10.83           (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 10.65/10.83        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 10.65/10.83        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 10.65/10.83        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 10.65/10.83             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 10.65/10.83        | (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ (k2_funct_1 @ sk_C)))),
% 10.65/10.83      inference('sup-', [status(thm)], ['27', '49'])).
% 10.65/10.83  thf('51', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 10.65/10.83      inference('simplify', [status(thm)], ['25'])).
% 10.65/10.83  thf('52', plain,
% 10.65/10.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('53', plain,
% 10.65/10.83      (![X32 : $i, X33 : $i, X34 : $i]:
% 10.65/10.83         (~ (v2_funct_1 @ X32)
% 10.65/10.83          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 10.65/10.83          | (v1_funct_2 @ (k2_funct_1 @ X32) @ X33 @ X34)
% 10.65/10.83          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 10.65/10.83          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 10.65/10.83          | ~ (v1_funct_1 @ X32))),
% 10.65/10.83      inference('cnf', [status(esa)], [t31_funct_2])).
% 10.65/10.83  thf('54', plain,
% 10.65/10.83      ((~ (v1_funct_1 @ sk_C)
% 10.65/10.83        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 10.65/10.83        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 10.65/10.83        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 10.65/10.83        | ~ (v2_funct_1 @ sk_C))),
% 10.65/10.83      inference('sup-', [status(thm)], ['52', '53'])).
% 10.65/10.83  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('56', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('57', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 10.65/10.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.83  thf('59', plain,
% 10.65/10.83      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 10.65/10.83      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 10.65/10.83  thf('60', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 10.65/10.83      inference('simplify', [status(thm)], ['59'])).
% 10.65/10.83  thf('61', plain,
% 10.65/10.83      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 10.65/10.83        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 10.65/10.84      inference('simplify', [status(thm)], ['10'])).
% 10.65/10.84  thf('62', plain,
% 10.65/10.84      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 10.65/10.84           (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 10.65/10.84        | (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ (k2_funct_1 @ sk_C)))),
% 10.65/10.84      inference('demod', [status(thm)], ['50', '51', '60', '61'])).
% 10.65/10.84  thf('63', plain,
% 10.65/10.84      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 10.65/10.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 10.65/10.84      inference('simplify', [status(thm)], ['10'])).
% 10.65/10.84  thf('64', plain,
% 10.65/10.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 10.65/10.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.84  thf(redefinition_r2_relset_1, axiom,
% 10.65/10.84    (![A:$i,B:$i,C:$i,D:$i]:
% 10.65/10.84     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.65/10.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.65/10.84       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 10.65/10.84  thf('65', plain,
% 10.65/10.84      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 10.65/10.84         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 10.65/10.84          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 10.65/10.84          | ((X7) = (X10))
% 10.65/10.84          | ~ (r2_relset_1 @ X8 @ X9 @ X7 @ X10))),
% 10.65/10.84      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 10.65/10.84  thf('66', plain,
% 10.65/10.84      (![X0 : $i]:
% 10.65/10.84         (~ (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ X0)
% 10.65/10.84          | ((sk_D_1) = (X0))
% 10.65/10.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 10.65/10.84      inference('sup-', [status(thm)], ['64', '65'])).
% 10.65/10.84  thf('67', plain,
% 10.65/10.84      ((((sk_D_1) = (k2_funct_1 @ sk_C))
% 10.65/10.84        | ~ (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ (k2_funct_1 @ sk_C)))),
% 10.65/10.84      inference('sup-', [status(thm)], ['63', '66'])).
% 10.65/10.84  thf('68', plain, (((sk_D_1) != (k2_funct_1 @ sk_C))),
% 10.65/10.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.84  thf('69', plain,
% 10.65/10.84      (~ (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ (k2_funct_1 @ sk_C))),
% 10.65/10.84      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 10.65/10.84  thf('70', plain,
% 10.65/10.84      (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 10.65/10.84          (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 10.65/10.84      inference('clc', [status(thm)], ['62', '69'])).
% 10.65/10.84  thf('71', plain,
% 10.65/10.84      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 10.65/10.84           (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 10.65/10.84        | ~ (v1_relat_1 @ sk_C)
% 10.65/10.84        | ~ (v1_funct_1 @ sk_C)
% 10.65/10.84        | ~ (v2_funct_1 @ sk_C))),
% 10.65/10.84      inference('sup-', [status(thm)], ['2', '70'])).
% 10.65/10.84  thf('72', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 10.65/10.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.84  thf(d1_funct_2, axiom,
% 10.65/10.84    (![A:$i,B:$i,C:$i]:
% 10.65/10.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.65/10.84       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.65/10.84           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 10.65/10.84             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 10.65/10.84         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.65/10.84           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 10.65/10.84             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 10.65/10.84  thf(zf_stmt_1, axiom,
% 10.65/10.84    (![C:$i,B:$i,A:$i]:
% 10.65/10.84     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 10.65/10.84       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 10.65/10.84  thf('73', plain,
% 10.65/10.84      (![X13 : $i, X14 : $i, X15 : $i]:
% 10.65/10.84         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 10.65/10.84          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 10.65/10.84          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 10.65/10.84      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.65/10.84  thf('74', plain,
% 10.65/10.84      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 10.65/10.84        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 10.65/10.84      inference('sup-', [status(thm)], ['72', '73'])).
% 10.65/10.84  thf(zf_stmt_2, axiom,
% 10.65/10.84    (![B:$i,A:$i]:
% 10.65/10.84     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.65/10.84       ( zip_tseitin_0 @ B @ A ) ))).
% 10.65/10.84  thf('75', plain,
% 10.65/10.84      (![X11 : $i, X12 : $i]:
% 10.65/10.84         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 10.65/10.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 10.65/10.84  thf('76', plain,
% 10.65/10.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.65/10.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.84  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 10.65/10.84  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 10.65/10.84  thf(zf_stmt_5, axiom,
% 10.65/10.84    (![A:$i,B:$i,C:$i]:
% 10.65/10.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.65/10.84       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 10.65/10.84         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.65/10.84           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 10.65/10.84             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 10.65/10.84  thf('77', plain,
% 10.65/10.84      (![X16 : $i, X17 : $i, X18 : $i]:
% 10.65/10.84         (~ (zip_tseitin_0 @ X16 @ X17)
% 10.65/10.84          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 10.65/10.84          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 10.65/10.84      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.65/10.84  thf('78', plain,
% 10.65/10.84      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 10.65/10.84      inference('sup-', [status(thm)], ['76', '77'])).
% 10.65/10.84  thf('79', plain,
% 10.65/10.84      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 10.65/10.84      inference('sup-', [status(thm)], ['75', '78'])).
% 10.65/10.84  thf('80', plain, (((sk_B) != (k1_xboole_0))),
% 10.65/10.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.84  thf('81', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 10.65/10.84      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 10.65/10.84  thf('82', plain,
% 10.65/10.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.65/10.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.84  thf(redefinition_k1_relset_1, axiom,
% 10.65/10.84    (![A:$i,B:$i,C:$i]:
% 10.65/10.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.65/10.84       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 10.65/10.84  thf('83', plain,
% 10.65/10.84      (![X4 : $i, X5 : $i, X6 : $i]:
% 10.65/10.84         (((k1_relset_1 @ X5 @ X6 @ X4) = (k1_relat_1 @ X4))
% 10.65/10.84          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 10.65/10.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.65/10.84  thf('84', plain,
% 10.65/10.84      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 10.65/10.84      inference('sup-', [status(thm)], ['82', '83'])).
% 10.65/10.84  thf('85', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 10.65/10.84      inference('demod', [status(thm)], ['74', '81', '84'])).
% 10.65/10.84  thf('86', plain,
% 10.65/10.84      ((r2_relset_1 @ sk_A @ sk_A @ 
% 10.65/10.84        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1) @ 
% 10.65/10.84        (k6_partfun1 @ sk_A))),
% 10.65/10.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.84  thf('87', plain,
% 10.65/10.84      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 10.65/10.84         = (k5_relat_1 @ sk_C @ sk_D_1))),
% 10.65/10.84      inference('demod', [status(thm)], ['30', '31'])).
% 10.65/10.84  thf('88', plain,
% 10.65/10.84      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 10.65/10.84        (k6_partfun1 @ sk_A))),
% 10.65/10.84      inference('demod', [status(thm)], ['86', '87'])).
% 10.65/10.84  thf('89', plain,
% 10.65/10.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.65/10.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.84  thf(cc1_relset_1, axiom,
% 10.65/10.84    (![A:$i,B:$i,C:$i]:
% 10.65/10.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.65/10.84       ( v1_relat_1 @ C ) ))).
% 10.65/10.84  thf('90', plain,
% 10.65/10.84      (![X1 : $i, X2 : $i, X3 : $i]:
% 10.65/10.84         ((v1_relat_1 @ X1)
% 10.65/10.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 10.65/10.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.65/10.84  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 10.65/10.84      inference('sup-', [status(thm)], ['89', '90'])).
% 10.65/10.84  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 10.65/10.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.84  thf('93', plain, ((v2_funct_1 @ sk_C)),
% 10.65/10.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.65/10.84  thf('94', plain, ($false),
% 10.65/10.84      inference('demod', [status(thm)], ['71', '85', '88', '91', '92', '93'])).
% 10.65/10.84  
% 10.65/10.84  % SZS output end Refutation
% 10.65/10.84  
% 10.65/10.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
