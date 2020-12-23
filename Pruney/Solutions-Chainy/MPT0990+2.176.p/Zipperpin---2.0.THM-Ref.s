%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IzfLfwi8Vb

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:25 EST 2020

% Result     : Theorem 12.15s
% Output     : Refutation 12.15s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 297 expanded)
%              Number of leaves         :   40 ( 105 expanded)
%              Depth                    :   14
%              Number of atoms          : 1564 (8431 expanded)
%              Number of equality atoms :   83 ( 572 expanded)
%              Maximal formula depth    :   26 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X26: $i] :
      ( ( k6_partfun1 @ X26 )
      = ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X33 )
       != X34 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 )
        = ( k5_relat_1 @ X20 @ X23 ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X33 )
       != X34 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ( X30 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X27 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X30 ) ) )
      | ( r2_relset_1 @ X27 @ X30 @ X32 @ X31 )
      | ~ ( r2_relset_1 @ X29 @ X30 @ ( k1_partfun1 @ X29 @ X27 @ X27 @ X30 @ X28 @ X32 ) @ ( k1_partfun1 @ X29 @ X27 @ X27 @ X30 @ X28 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X27 @ X30 )
      | ~ ( v1_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X29 @ X27 @ X28 )
       != X27 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X33 )
       != X34 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X33 ) @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( X8 = X11 )
      | ~ ( r2_relset_1 @ X9 @ X10 @ X8 @ X11 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('92',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['71','85','88','93','94','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IzfLfwi8Vb
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 12.15/12.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.15/12.35  % Solved by: fo/fo7.sh
% 12.15/12.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.15/12.35  % done 1539 iterations in 11.896s
% 12.15/12.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.15/12.35  % SZS output start Refutation
% 12.15/12.35  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 12.15/12.35  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 12.15/12.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.15/12.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.15/12.35  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 12.15/12.35  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 12.15/12.35  thf(sk_C_type, type, sk_C: $i).
% 12.15/12.35  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 12.15/12.35  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 12.15/12.35  thf(sk_D_1_type, type, sk_D_1: $i).
% 12.15/12.35  thf(sk_A_type, type, sk_A: $i).
% 12.15/12.35  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 12.15/12.35  thf(sk_B_type, type, sk_B: $i).
% 12.15/12.35  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 12.15/12.35  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 12.15/12.35  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 12.15/12.35  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 12.15/12.35  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 12.15/12.35  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 12.15/12.35  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 12.15/12.35  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 12.15/12.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.15/12.35  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 12.15/12.35  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 12.15/12.35  thf(t61_funct_1, axiom,
% 12.15/12.35    (![A:$i]:
% 12.15/12.35     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 12.15/12.35       ( ( v2_funct_1 @ A ) =>
% 12.15/12.35         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 12.15/12.35             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 12.15/12.35           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 12.15/12.35             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 12.15/12.35  thf('0', plain,
% 12.15/12.35      (![X4 : $i]:
% 12.15/12.35         (~ (v2_funct_1 @ X4)
% 12.15/12.35          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 12.15/12.35              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 12.15/12.35          | ~ (v1_funct_1 @ X4)
% 12.15/12.35          | ~ (v1_relat_1 @ X4))),
% 12.15/12.35      inference('cnf', [status(esa)], [t61_funct_1])).
% 12.15/12.35  thf(redefinition_k6_partfun1, axiom,
% 12.15/12.35    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 12.15/12.35  thf('1', plain, (![X26 : $i]: ((k6_partfun1 @ X26) = (k6_relat_1 @ X26))),
% 12.15/12.35      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 12.15/12.35  thf('2', plain,
% 12.15/12.35      (![X4 : $i]:
% 12.15/12.35         (~ (v2_funct_1 @ X4)
% 12.15/12.35          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 12.15/12.35              = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 12.15/12.35          | ~ (v1_funct_1 @ X4)
% 12.15/12.35          | ~ (v1_relat_1 @ X4))),
% 12.15/12.35      inference('demod', [status(thm)], ['0', '1'])).
% 12.15/12.35  thf(t36_funct_2, conjecture,
% 12.15/12.35    (![A:$i,B:$i,C:$i]:
% 12.15/12.35     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 12.15/12.35         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.15/12.35       ( ![D:$i]:
% 12.15/12.35         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 12.15/12.35             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 12.15/12.35           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 12.15/12.35               ( r2_relset_1 @
% 12.15/12.35                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 12.15/12.35                 ( k6_partfun1 @ A ) ) & 
% 12.15/12.35               ( v2_funct_1 @ C ) ) =>
% 12.15/12.35             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 12.15/12.35               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 12.15/12.35  thf(zf_stmt_0, negated_conjecture,
% 12.15/12.35    (~( ![A:$i,B:$i,C:$i]:
% 12.15/12.35        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 12.15/12.35            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.15/12.35          ( ![D:$i]:
% 12.15/12.35            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 12.15/12.35                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 12.15/12.35              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 12.15/12.35                  ( r2_relset_1 @
% 12.15/12.35                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 12.15/12.35                    ( k6_partfun1 @ A ) ) & 
% 12.15/12.35                  ( v2_funct_1 @ C ) ) =>
% 12.15/12.35                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 12.15/12.35                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 12.15/12.35    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 12.15/12.35  thf('3', plain,
% 12.15/12.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.15/12.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.35  thf(t31_funct_2, axiom,
% 12.15/12.35    (![A:$i,B:$i,C:$i]:
% 12.15/12.35     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 12.15/12.35         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.15/12.35       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 12.15/12.35         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 12.15/12.35           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 12.15/12.35           ( m1_subset_1 @
% 12.15/12.35             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 12.15/12.35  thf('4', plain,
% 12.15/12.35      (![X33 : $i, X34 : $i, X35 : $i]:
% 12.15/12.35         (~ (v2_funct_1 @ X33)
% 12.15/12.35          | ((k2_relset_1 @ X35 @ X34 @ X33) != (X34))
% 12.15/12.35          | (m1_subset_1 @ (k2_funct_1 @ X33) @ 
% 12.15/12.35             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 12.15/12.35          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 12.15/12.35          | ~ (v1_funct_2 @ X33 @ X35 @ X34)
% 12.15/12.35          | ~ (v1_funct_1 @ X33))),
% 12.15/12.35      inference('cnf', [status(esa)], [t31_funct_2])).
% 12.15/12.35  thf('5', plain,
% 12.15/12.35      ((~ (v1_funct_1 @ sk_C)
% 12.15/12.35        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 12.15/12.35        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.15/12.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 12.15/12.35        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 12.15/12.35        | ~ (v2_funct_1 @ sk_C))),
% 12.15/12.35      inference('sup-', [status(thm)], ['3', '4'])).
% 12.15/12.35  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 12.15/12.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.35  thf('7', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 12.15/12.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.35  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 12.15/12.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.35  thf('9', plain, ((v2_funct_1 @ sk_C)),
% 12.15/12.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.35  thf('10', plain,
% 12.15/12.35      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.15/12.35         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 12.15/12.35        | ((sk_B) != (sk_B)))),
% 12.15/12.35      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 12.15/12.35  thf('11', plain,
% 12.15/12.35      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.15/12.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 12.15/12.35      inference('simplify', [status(thm)], ['10'])).
% 12.15/12.35  thf('12', plain,
% 12.15/12.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.15/12.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.35  thf(redefinition_k1_partfun1, axiom,
% 12.15/12.35    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 12.15/12.35     ( ( ( v1_funct_1 @ E ) & 
% 12.15/12.35         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 12.15/12.35         ( v1_funct_1 @ F ) & 
% 12.15/12.35         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 12.15/12.35       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 12.15/12.35  thf('13', plain,
% 12.15/12.35      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 12.15/12.35         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 12.15/12.35          | ~ (v1_funct_1 @ X20)
% 12.15/12.35          | ~ (v1_funct_1 @ X23)
% 12.15/12.35          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 12.15/12.35          | ((k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23)
% 12.15/12.35              = (k5_relat_1 @ X20 @ X23)))),
% 12.15/12.35      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 12.15/12.35  thf('14', plain,
% 12.15/12.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.35         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 12.15/12.35            = (k5_relat_1 @ sk_C @ X0))
% 12.15/12.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 12.15/12.35          | ~ (v1_funct_1 @ X0)
% 12.15/12.35          | ~ (v1_funct_1 @ sk_C))),
% 12.15/12.35      inference('sup-', [status(thm)], ['12', '13'])).
% 12.15/12.35  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 12.15/12.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.35  thf('16', plain,
% 12.15/12.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.35         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 12.15/12.35            = (k5_relat_1 @ sk_C @ X0))
% 12.15/12.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 12.15/12.35          | ~ (v1_funct_1 @ X0))),
% 12.15/12.35      inference('demod', [status(thm)], ['14', '15'])).
% 12.15/12.35  thf('17', plain,
% 12.15/12.35      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 12.15/12.35        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 12.15/12.35            (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 12.15/12.35      inference('sup-', [status(thm)], ['11', '16'])).
% 12.15/12.35  thf('18', plain,
% 12.15/12.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.15/12.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.35  thf('19', plain,
% 12.15/12.35      (![X33 : $i, X34 : $i, X35 : $i]:
% 12.15/12.35         (~ (v2_funct_1 @ X33)
% 12.15/12.35          | ((k2_relset_1 @ X35 @ X34 @ X33) != (X34))
% 12.15/12.35          | (v1_funct_1 @ (k2_funct_1 @ X33))
% 12.15/12.35          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 12.15/12.35          | ~ (v1_funct_2 @ X33 @ X35 @ X34)
% 12.15/12.35          | ~ (v1_funct_1 @ X33))),
% 12.15/12.35      inference('cnf', [status(esa)], [t31_funct_2])).
% 12.15/12.35  thf('20', plain,
% 12.15/12.35      ((~ (v1_funct_1 @ sk_C)
% 12.15/12.35        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 12.15/12.35        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 12.15/12.35        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 12.15/12.35        | ~ (v2_funct_1 @ sk_C))),
% 12.15/12.35      inference('sup-', [status(thm)], ['18', '19'])).
% 12.15/12.35  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 12.15/12.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.35  thf('22', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 12.15/12.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.35  thf('23', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 12.15/12.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.35  thf('24', plain, ((v2_funct_1 @ sk_C)),
% 12.15/12.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.35  thf('25', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)) | ((sk_B) != (sk_B)))),
% 12.15/12.35      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 12.15/12.35  thf('26', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 12.15/12.35      inference('simplify', [status(thm)], ['25'])).
% 12.15/12.35  thf('27', plain,
% 12.15/12.35      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 12.15/12.35         = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 12.15/12.35      inference('demod', [status(thm)], ['17', '26'])).
% 12.15/12.35  thf('28', plain,
% 12.15/12.35      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 12.15/12.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.35  thf('29', plain,
% 12.15/12.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.35         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 12.15/12.35            = (k5_relat_1 @ sk_C @ X0))
% 12.15/12.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 12.15/12.35          | ~ (v1_funct_1 @ X0))),
% 12.15/12.35      inference('demod', [status(thm)], ['14', '15'])).
% 12.15/12.35  thf('30', plain,
% 12.15/12.35      ((~ (v1_funct_1 @ sk_D_1)
% 12.15/12.35        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 12.15/12.35            = (k5_relat_1 @ sk_C @ sk_D_1)))),
% 12.15/12.35      inference('sup-', [status(thm)], ['28', '29'])).
% 12.15/12.35  thf('31', plain, ((v1_funct_1 @ sk_D_1)),
% 12.15/12.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.35  thf('32', plain,
% 12.15/12.35      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 12.15/12.35         = (k5_relat_1 @ sk_C @ sk_D_1))),
% 12.15/12.35      inference('demod', [status(thm)], ['30', '31'])).
% 12.15/12.35  thf('33', plain,
% 12.15/12.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.15/12.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.35  thf(t22_funct_2, axiom,
% 12.15/12.35    (![A:$i,B:$i,C:$i]:
% 12.15/12.35     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 12.15/12.35         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.15/12.35       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 12.15/12.35         ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) <=>
% 12.15/12.36           ( ![D:$i]:
% 12.15/12.36             ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 12.15/12.36               ( ![E:$i]:
% 12.15/12.36                 ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ D ) & 
% 12.15/12.36                     ( m1_subset_1 @
% 12.15/12.36                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) =>
% 12.15/12.36                   ( ![F:$i]:
% 12.15/12.36                     ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ B @ D ) & 
% 12.15/12.36                         ( m1_subset_1 @
% 12.15/12.36                           F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) =>
% 12.15/12.36                       ( ( r2_relset_1 @
% 12.15/12.36                           A @ D @ ( k1_partfun1 @ A @ B @ B @ D @ C @ E ) @ 
% 12.15/12.36                           ( k1_partfun1 @ A @ B @ B @ D @ C @ F ) ) =>
% 12.15/12.36                         ( r2_relset_1 @ B @ D @ E @ F ) ) ) ) ) ) ) ) ) ) ))).
% 12.15/12.36  thf('34', plain,
% 12.15/12.36      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 12.15/12.36         (((X27) = (k1_xboole_0))
% 12.15/12.36          | ~ (v1_funct_1 @ X28)
% 12.15/12.36          | ~ (v1_funct_2 @ X28 @ X29 @ X27)
% 12.15/12.36          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 12.15/12.36          | ((X30) = (k1_xboole_0))
% 12.15/12.36          | ~ (v1_funct_1 @ X31)
% 12.15/12.36          | ~ (v1_funct_2 @ X31 @ X27 @ X30)
% 12.15/12.36          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X30)))
% 12.15/12.36          | (r2_relset_1 @ X27 @ X30 @ X32 @ X31)
% 12.15/12.36          | ~ (r2_relset_1 @ X29 @ X30 @ 
% 12.15/12.36               (k1_partfun1 @ X29 @ X27 @ X27 @ X30 @ X28 @ X32) @ 
% 12.15/12.36               (k1_partfun1 @ X29 @ X27 @ X27 @ X30 @ X28 @ X31))
% 12.15/12.36          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X30)))
% 12.15/12.36          | ~ (v1_funct_2 @ X32 @ X27 @ X30)
% 12.15/12.36          | ~ (v1_funct_1 @ X32)
% 12.15/12.36          | ((k2_relset_1 @ X29 @ X27 @ X28) != (X27)))),
% 12.15/12.36      inference('cnf', [status(esa)], [t22_funct_2])).
% 12.15/12.36  thf('35', plain,
% 12.15/12.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.36         (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 12.15/12.36          | ~ (v1_funct_1 @ X0)
% 12.15/12.36          | ~ (v1_funct_2 @ X0 @ sk_B @ X1)
% 12.15/12.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 12.15/12.36          | ~ (r2_relset_1 @ sk_A @ X1 @ 
% 12.15/12.36               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0) @ 
% 12.15/12.36               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2))
% 12.15/12.36          | (r2_relset_1 @ sk_B @ X1 @ X0 @ X2)
% 12.15/12.36          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 12.15/12.36          | ~ (v1_funct_2 @ X2 @ sk_B @ X1)
% 12.15/12.36          | ~ (v1_funct_1 @ X2)
% 12.15/12.36          | ((X1) = (k1_xboole_0))
% 12.15/12.36          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 12.15/12.36          | ~ (v1_funct_1 @ sk_C)
% 12.15/12.36          | ((sk_B) = (k1_xboole_0)))),
% 12.15/12.36      inference('sup-', [status(thm)], ['33', '34'])).
% 12.15/12.36  thf('36', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('37', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('39', plain,
% 12.15/12.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.36         (((sk_B) != (sk_B))
% 12.15/12.36          | ~ (v1_funct_1 @ X0)
% 12.15/12.36          | ~ (v1_funct_2 @ X0 @ sk_B @ X1)
% 12.15/12.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 12.15/12.36          | ~ (r2_relset_1 @ sk_A @ X1 @ 
% 12.15/12.36               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0) @ 
% 12.15/12.36               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2))
% 12.15/12.36          | (r2_relset_1 @ sk_B @ X1 @ X0 @ X2)
% 12.15/12.36          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 12.15/12.36          | ~ (v1_funct_2 @ X2 @ sk_B @ X1)
% 12.15/12.36          | ~ (v1_funct_1 @ X2)
% 12.15/12.36          | ((X1) = (k1_xboole_0))
% 12.15/12.36          | ((sk_B) = (k1_xboole_0)))),
% 12.15/12.36      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 12.15/12.36  thf('40', plain,
% 12.15/12.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.36         (((sk_B) = (k1_xboole_0))
% 12.15/12.36          | ((X1) = (k1_xboole_0))
% 12.15/12.36          | ~ (v1_funct_1 @ X2)
% 12.15/12.36          | ~ (v1_funct_2 @ X2 @ sk_B @ X1)
% 12.15/12.36          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 12.15/12.36          | (r2_relset_1 @ sk_B @ X1 @ X0 @ X2)
% 12.15/12.36          | ~ (r2_relset_1 @ sk_A @ X1 @ 
% 12.15/12.36               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0) @ 
% 12.15/12.36               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2))
% 12.15/12.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 12.15/12.36          | ~ (v1_funct_2 @ X0 @ sk_B @ X1)
% 12.15/12.36          | ~ (v1_funct_1 @ X0))),
% 12.15/12.36      inference('simplify', [status(thm)], ['39'])).
% 12.15/12.36  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('42', plain,
% 12.15/12.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.36         (((X1) = (k1_xboole_0))
% 12.15/12.36          | ~ (v1_funct_1 @ X2)
% 12.15/12.36          | ~ (v1_funct_2 @ X2 @ sk_B @ X1)
% 12.15/12.36          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 12.15/12.36          | (r2_relset_1 @ sk_B @ X1 @ X0 @ X2)
% 12.15/12.36          | ~ (r2_relset_1 @ sk_A @ X1 @ 
% 12.15/12.36               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0) @ 
% 12.15/12.36               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2))
% 12.15/12.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 12.15/12.36          | ~ (v1_funct_2 @ X0 @ sk_B @ X1)
% 12.15/12.36          | ~ (v1_funct_1 @ X0))),
% 12.15/12.36      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 12.15/12.36  thf('43', plain,
% 12.15/12.36      (![X0 : $i]:
% 12.15/12.36         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 12.15/12.36             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0))
% 12.15/12.36          | ~ (v1_funct_1 @ sk_D_1)
% 12.15/12.36          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_A)
% 12.15/12.36          | ~ (m1_subset_1 @ sk_D_1 @ 
% 12.15/12.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 12.15/12.36          | (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ X0)
% 12.15/12.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 12.15/12.36          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 12.15/12.36          | ~ (v1_funct_1 @ X0)
% 12.15/12.36          | ((sk_A) = (k1_xboole_0)))),
% 12.15/12.36      inference('sup-', [status(thm)], ['32', '42'])).
% 12.15/12.36  thf('44', plain, ((v1_funct_1 @ sk_D_1)),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('45', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_A)),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('46', plain,
% 12.15/12.36      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('47', plain,
% 12.15/12.36      (![X0 : $i]:
% 12.15/12.36         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 12.15/12.36             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0))
% 12.15/12.36          | (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ X0)
% 12.15/12.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 12.15/12.36          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 12.15/12.36          | ~ (v1_funct_1 @ X0)
% 12.15/12.36          | ((sk_A) = (k1_xboole_0)))),
% 12.15/12.36      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 12.15/12.36  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('49', plain,
% 12.15/12.36      (![X0 : $i]:
% 12.15/12.36         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 12.15/12.36             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0))
% 12.15/12.36          | (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ X0)
% 12.15/12.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 12.15/12.36          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 12.15/12.36          | ~ (v1_funct_1 @ X0))),
% 12.15/12.36      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 12.15/12.36  thf('50', plain,
% 12.15/12.36      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 12.15/12.36           (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 12.15/12.36        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 12.15/12.36        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 12.15/12.36        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.15/12.36             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 12.15/12.36        | (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ (k2_funct_1 @ sk_C)))),
% 12.15/12.36      inference('sup-', [status(thm)], ['27', '49'])).
% 12.15/12.36  thf('51', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 12.15/12.36      inference('simplify', [status(thm)], ['25'])).
% 12.15/12.36  thf('52', plain,
% 12.15/12.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('53', plain,
% 12.15/12.36      (![X33 : $i, X34 : $i, X35 : $i]:
% 12.15/12.36         (~ (v2_funct_1 @ X33)
% 12.15/12.36          | ((k2_relset_1 @ X35 @ X34 @ X33) != (X34))
% 12.15/12.36          | (v1_funct_2 @ (k2_funct_1 @ X33) @ X34 @ X35)
% 12.15/12.36          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 12.15/12.36          | ~ (v1_funct_2 @ X33 @ X35 @ X34)
% 12.15/12.36          | ~ (v1_funct_1 @ X33))),
% 12.15/12.36      inference('cnf', [status(esa)], [t31_funct_2])).
% 12.15/12.36  thf('54', plain,
% 12.15/12.36      ((~ (v1_funct_1 @ sk_C)
% 12.15/12.36        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 12.15/12.36        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 12.15/12.36        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 12.15/12.36        | ~ (v2_funct_1 @ sk_C))),
% 12.15/12.36      inference('sup-', [status(thm)], ['52', '53'])).
% 12.15/12.36  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('56', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('57', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('59', plain,
% 12.15/12.36      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 12.15/12.36      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 12.15/12.36  thf('60', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 12.15/12.36      inference('simplify', [status(thm)], ['59'])).
% 12.15/12.36  thf('61', plain,
% 12.15/12.36      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.15/12.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 12.15/12.36      inference('simplify', [status(thm)], ['10'])).
% 12.15/12.36  thf('62', plain,
% 12.15/12.36      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 12.15/12.36           (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 12.15/12.36        | (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ (k2_funct_1 @ sk_C)))),
% 12.15/12.36      inference('demod', [status(thm)], ['50', '51', '60', '61'])).
% 12.15/12.36  thf('63', plain,
% 12.15/12.36      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.15/12.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 12.15/12.36      inference('simplify', [status(thm)], ['10'])).
% 12.15/12.36  thf('64', plain,
% 12.15/12.36      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf(redefinition_r2_relset_1, axiom,
% 12.15/12.36    (![A:$i,B:$i,C:$i,D:$i]:
% 12.15/12.36     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 12.15/12.36         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.15/12.36       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 12.15/12.36  thf('65', plain,
% 12.15/12.36      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 12.15/12.36         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 12.15/12.36          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 12.15/12.36          | ((X8) = (X11))
% 12.15/12.36          | ~ (r2_relset_1 @ X9 @ X10 @ X8 @ X11))),
% 12.15/12.36      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 12.15/12.36  thf('66', plain,
% 12.15/12.36      (![X0 : $i]:
% 12.15/12.36         (~ (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ X0)
% 12.15/12.36          | ((sk_D_1) = (X0))
% 12.15/12.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 12.15/12.36      inference('sup-', [status(thm)], ['64', '65'])).
% 12.15/12.36  thf('67', plain,
% 12.15/12.36      ((((sk_D_1) = (k2_funct_1 @ sk_C))
% 12.15/12.36        | ~ (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ (k2_funct_1 @ sk_C)))),
% 12.15/12.36      inference('sup-', [status(thm)], ['63', '66'])).
% 12.15/12.36  thf('68', plain, (((sk_D_1) != (k2_funct_1 @ sk_C))),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('69', plain,
% 12.15/12.36      (~ (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ (k2_funct_1 @ sk_C))),
% 12.15/12.36      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 12.15/12.36  thf('70', plain,
% 12.15/12.36      (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 12.15/12.36          (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 12.15/12.36      inference('clc', [status(thm)], ['62', '69'])).
% 12.15/12.36  thf('71', plain,
% 12.15/12.36      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 12.15/12.36           (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 12.15/12.36        | ~ (v1_relat_1 @ sk_C)
% 12.15/12.36        | ~ (v1_funct_1 @ sk_C)
% 12.15/12.36        | ~ (v2_funct_1 @ sk_C))),
% 12.15/12.36      inference('sup-', [status(thm)], ['2', '70'])).
% 12.15/12.36  thf('72', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf(d1_funct_2, axiom,
% 12.15/12.36    (![A:$i,B:$i,C:$i]:
% 12.15/12.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.15/12.36       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 12.15/12.36           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 12.15/12.36             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 12.15/12.36         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 12.15/12.36           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 12.15/12.36             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 12.15/12.36  thf(zf_stmt_1, axiom,
% 12.15/12.36    (![C:$i,B:$i,A:$i]:
% 12.15/12.36     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 12.15/12.36       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 12.15/12.36  thf('73', plain,
% 12.15/12.36      (![X14 : $i, X15 : $i, X16 : $i]:
% 12.15/12.36         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 12.15/12.36          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 12.15/12.36          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 12.15/12.36  thf('74', plain,
% 12.15/12.36      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 12.15/12.36        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 12.15/12.36      inference('sup-', [status(thm)], ['72', '73'])).
% 12.15/12.36  thf(zf_stmt_2, axiom,
% 12.15/12.36    (![B:$i,A:$i]:
% 12.15/12.36     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 12.15/12.36       ( zip_tseitin_0 @ B @ A ) ))).
% 12.15/12.36  thf('75', plain,
% 12.15/12.36      (![X12 : $i, X13 : $i]:
% 12.15/12.36         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_2])).
% 12.15/12.36  thf('76', plain,
% 12.15/12.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 12.15/12.36  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 12.15/12.36  thf(zf_stmt_5, axiom,
% 12.15/12.36    (![A:$i,B:$i,C:$i]:
% 12.15/12.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.15/12.36       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 12.15/12.36         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 12.15/12.36           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 12.15/12.36             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 12.15/12.36  thf('77', plain,
% 12.15/12.36      (![X17 : $i, X18 : $i, X19 : $i]:
% 12.15/12.36         (~ (zip_tseitin_0 @ X17 @ X18)
% 12.15/12.36          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 12.15/12.36          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 12.15/12.36  thf('78', plain,
% 12.15/12.36      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 12.15/12.36      inference('sup-', [status(thm)], ['76', '77'])).
% 12.15/12.36  thf('79', plain,
% 12.15/12.36      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 12.15/12.36      inference('sup-', [status(thm)], ['75', '78'])).
% 12.15/12.36  thf('80', plain, (((sk_B) != (k1_xboole_0))),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('81', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 12.15/12.36      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 12.15/12.36  thf('82', plain,
% 12.15/12.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf(redefinition_k1_relset_1, axiom,
% 12.15/12.36    (![A:$i,B:$i,C:$i]:
% 12.15/12.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.15/12.36       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 12.15/12.36  thf('83', plain,
% 12.15/12.36      (![X5 : $i, X6 : $i, X7 : $i]:
% 12.15/12.36         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 12.15/12.36          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 12.15/12.36      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 12.15/12.36  thf('84', plain,
% 12.15/12.36      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 12.15/12.36      inference('sup-', [status(thm)], ['82', '83'])).
% 12.15/12.36  thf('85', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 12.15/12.36      inference('demod', [status(thm)], ['74', '81', '84'])).
% 12.15/12.36  thf('86', plain,
% 12.15/12.36      ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.15/12.36        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1) @ 
% 12.15/12.36        (k6_partfun1 @ sk_A))),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('87', plain,
% 12.15/12.36      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 12.15/12.36         = (k5_relat_1 @ sk_C @ sk_D_1))),
% 12.15/12.36      inference('demod', [status(thm)], ['30', '31'])).
% 12.15/12.36  thf('88', plain,
% 12.15/12.36      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 12.15/12.36        (k6_partfun1 @ sk_A))),
% 12.15/12.36      inference('demod', [status(thm)], ['86', '87'])).
% 12.15/12.36  thf('89', plain,
% 12.15/12.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf(cc2_relat_1, axiom,
% 12.15/12.36    (![A:$i]:
% 12.15/12.36     ( ( v1_relat_1 @ A ) =>
% 12.15/12.36       ( ![B:$i]:
% 12.15/12.36         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 12.15/12.36  thf('90', plain,
% 12.15/12.36      (![X0 : $i, X1 : $i]:
% 12.15/12.36         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 12.15/12.36          | (v1_relat_1 @ X0)
% 12.15/12.36          | ~ (v1_relat_1 @ X1))),
% 12.15/12.36      inference('cnf', [status(esa)], [cc2_relat_1])).
% 12.15/12.36  thf('91', plain,
% 12.15/12.36      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 12.15/12.36      inference('sup-', [status(thm)], ['89', '90'])).
% 12.15/12.36  thf(fc6_relat_1, axiom,
% 12.15/12.36    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 12.15/12.36  thf('92', plain,
% 12.15/12.36      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 12.15/12.36      inference('cnf', [status(esa)], [fc6_relat_1])).
% 12.15/12.36  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 12.15/12.36      inference('demod', [status(thm)], ['91', '92'])).
% 12.15/12.36  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 12.15/12.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.15/12.36  thf('96', plain, ($false),
% 12.15/12.36      inference('demod', [status(thm)], ['71', '85', '88', '93', '94', '95'])).
% 12.15/12.36  
% 12.15/12.36  % SZS output end Refutation
% 12.15/12.36  
% 12.15/12.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
