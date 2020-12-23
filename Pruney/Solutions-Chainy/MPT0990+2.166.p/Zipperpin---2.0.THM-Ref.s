%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nP6UW9juoI

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:23 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 283 expanded)
%              Number of leaves         :   42 ( 103 expanded)
%              Depth                    :   15
%              Number of atoms          : 1386 (6694 expanded)
%              Number of equality atoms :   92 ( 478 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

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

thf('0',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( X10 = X13 )
      | ~ ( r2_relset_1 @ X11 @ X12 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('24',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( X5
        = ( k2_funct_1 @ X6 ) )
      | ( ( k5_relat_1 @ X6 @ X5 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('29',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( X5
        = ( k2_funct_1 @ X6 ) )
      | ( ( k5_relat_1 @ X6 @ X5 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X6 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ( X17
        = ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
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

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('38',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['34','41','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v2_funct_1 @ X36 )
      | ( ( k2_relset_1 @ X38 @ X37 @ X36 )
       != X37 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('64',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v2_funct_1 @ X36 )
      | ( ( k2_relset_1 @ X38 @ X37 @ X36 )
       != X37 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X36 ) @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('67',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ( X17
        = ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('75',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('77',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('78',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('79',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('83',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','82'])).

thf('84',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['64','83'])).

thf('85',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['53','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('87',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ( X17
        = ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('92',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('94',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('96',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('102',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['92','99','102'])).

thf('104',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('107',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('109',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_B != sk_B )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','45','50','51','52','89','103','104','109'])).

thf('111',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['111','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nP6UW9juoI
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.82/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.82/1.03  % Solved by: fo/fo7.sh
% 0.82/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.03  % done 327 iterations in 0.575s
% 0.82/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.82/1.03  % SZS output start Refutation
% 0.82/1.03  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.82/1.03  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.82/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.03  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.82/1.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.82/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.82/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.82/1.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.82/1.03  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.82/1.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.82/1.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.82/1.03  thf(sk_C_type, type, sk_C: $i).
% 0.82/1.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.82/1.03  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.82/1.03  thf(sk_D_type, type, sk_D: $i).
% 0.82/1.03  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.82/1.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.82/1.03  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.82/1.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.82/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.03  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.82/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/1.03  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.82/1.03  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.82/1.03  thf(t36_funct_2, conjecture,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.82/1.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.03       ( ![D:$i]:
% 0.82/1.03         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.82/1.03             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.82/1.03           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.82/1.03               ( r2_relset_1 @
% 0.82/1.03                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.82/1.03                 ( k6_partfun1 @ A ) ) & 
% 0.82/1.03               ( v2_funct_1 @ C ) ) =>
% 0.82/1.03             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.82/1.03               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.82/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.03    (~( ![A:$i,B:$i,C:$i]:
% 0.82/1.03        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.82/1.03            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.03          ( ![D:$i]:
% 0.82/1.03            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.82/1.03                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.82/1.03              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.82/1.03                  ( r2_relset_1 @
% 0.82/1.03                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.82/1.03                    ( k6_partfun1 @ A ) ) & 
% 0.82/1.03                  ( v2_funct_1 @ C ) ) =>
% 0.82/1.03                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.82/1.03                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.82/1.03    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.82/1.03  thf('0', plain,
% 0.82/1.03      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.82/1.03        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.82/1.03        (k6_partfun1 @ sk_A))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('1', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('2', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(redefinition_k1_partfun1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.82/1.03     ( ( ( v1_funct_1 @ E ) & 
% 0.82/1.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.82/1.03         ( v1_funct_1 @ F ) & 
% 0.82/1.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.82/1.03       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.82/1.03  thf('3', plain,
% 0.82/1.03      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.82/1.03         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.82/1.03          | ~ (v1_funct_1 @ X29)
% 0.82/1.03          | ~ (v1_funct_1 @ X32)
% 0.82/1.03          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.82/1.03          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 0.82/1.03              = (k5_relat_1 @ X29 @ X32)))),
% 0.82/1.03      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.82/1.03  thf('4', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.82/1.03            = (k5_relat_1 @ sk_C @ X0))
% 0.82/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.82/1.03          | ~ (v1_funct_1 @ X0)
% 0.82/1.03          | ~ (v1_funct_1 @ sk_C))),
% 0.82/1.03      inference('sup-', [status(thm)], ['2', '3'])).
% 0.82/1.03  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('6', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.82/1.03            = (k5_relat_1 @ sk_C @ X0))
% 0.82/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.82/1.03          | ~ (v1_funct_1 @ X0))),
% 0.82/1.03      inference('demod', [status(thm)], ['4', '5'])).
% 0.82/1.03  thf('7', plain,
% 0.82/1.03      ((~ (v1_funct_1 @ sk_D)
% 0.82/1.03        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.82/1.03            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['1', '6'])).
% 0.82/1.03  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('9', plain,
% 0.82/1.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.82/1.03         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.82/1.03      inference('demod', [status(thm)], ['7', '8'])).
% 0.82/1.03  thf('10', plain,
% 0.82/1.03      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.82/1.03        (k6_partfun1 @ sk_A))),
% 0.82/1.03      inference('demod', [status(thm)], ['0', '9'])).
% 0.82/1.03  thf('11', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('12', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(dt_k1_partfun1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.82/1.03     ( ( ( v1_funct_1 @ E ) & 
% 0.82/1.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.82/1.03         ( v1_funct_1 @ F ) & 
% 0.82/1.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.82/1.03       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.82/1.03         ( m1_subset_1 @
% 0.82/1.03           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.82/1.03           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.82/1.03  thf('13', plain,
% 0.82/1.03      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.82/1.03         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.82/1.03          | ~ (v1_funct_1 @ X23)
% 0.82/1.03          | ~ (v1_funct_1 @ X26)
% 0.82/1.03          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.82/1.03          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 0.82/1.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 0.82/1.03      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.82/1.03  thf('14', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.82/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.82/1.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.82/1.03          | ~ (v1_funct_1 @ X1)
% 0.82/1.03          | ~ (v1_funct_1 @ sk_C))),
% 0.82/1.03      inference('sup-', [status(thm)], ['12', '13'])).
% 0.82/1.03  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('16', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.82/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.82/1.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.82/1.03          | ~ (v1_funct_1 @ X1))),
% 0.82/1.03      inference('demod', [status(thm)], ['14', '15'])).
% 0.82/1.03  thf('17', plain,
% 0.82/1.03      ((~ (v1_funct_1 @ sk_D)
% 0.82/1.03        | (m1_subset_1 @ 
% 0.82/1.03           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.82/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.82/1.03      inference('sup-', [status(thm)], ['11', '16'])).
% 0.82/1.03  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('19', plain,
% 0.82/1.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.82/1.03         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.82/1.03      inference('demod', [status(thm)], ['7', '8'])).
% 0.82/1.03  thf('20', plain,
% 0.82/1.03      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.82/1.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.82/1.03      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.82/1.03  thf(redefinition_r2_relset_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.03     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.82/1.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.03       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.82/1.03  thf('21', plain,
% 0.82/1.03      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.82/1.03         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.82/1.03          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.82/1.03          | ((X10) = (X13))
% 0.82/1.03          | ~ (r2_relset_1 @ X11 @ X12 @ X10 @ X13))),
% 0.82/1.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.82/1.03  thf('22', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.82/1.03          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.82/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.82/1.03      inference('sup-', [status(thm)], ['20', '21'])).
% 0.82/1.03  thf('23', plain,
% 0.82/1.03      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.82/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.82/1.03        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['10', '22'])).
% 0.82/1.03  thf(t29_relset_1, axiom,
% 0.82/1.03    (![A:$i]:
% 0.82/1.03     ( m1_subset_1 @
% 0.82/1.03       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.82/1.03  thf('24', plain,
% 0.82/1.03      (![X14 : $i]:
% 0.82/1.03         (m1_subset_1 @ (k6_relat_1 @ X14) @ 
% 0.82/1.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.82/1.03  thf(redefinition_k6_partfun1, axiom,
% 0.82/1.03    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.82/1.03  thf('25', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.82/1.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.82/1.03  thf('26', plain,
% 0.82/1.03      (![X14 : $i]:
% 0.82/1.03         (m1_subset_1 @ (k6_partfun1 @ X14) @ 
% 0.82/1.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))),
% 0.82/1.03      inference('demod', [status(thm)], ['24', '25'])).
% 0.82/1.03  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.82/1.03      inference('demod', [status(thm)], ['23', '26'])).
% 0.82/1.03  thf(t63_funct_1, axiom,
% 0.82/1.03    (![A:$i]:
% 0.82/1.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.82/1.03       ( ![B:$i]:
% 0.82/1.03         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.82/1.03           ( ( ( v2_funct_1 @ A ) & 
% 0.82/1.03               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.82/1.03               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.82/1.03             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.82/1.03  thf('28', plain,
% 0.82/1.03      (![X5 : $i, X6 : $i]:
% 0.82/1.03         (~ (v1_relat_1 @ X5)
% 0.82/1.03          | ~ (v1_funct_1 @ X5)
% 0.82/1.03          | ((X5) = (k2_funct_1 @ X6))
% 0.82/1.03          | ((k5_relat_1 @ X6 @ X5) != (k6_relat_1 @ (k1_relat_1 @ X6)))
% 0.82/1.03          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X5))
% 0.82/1.03          | ~ (v2_funct_1 @ X6)
% 0.82/1.03          | ~ (v1_funct_1 @ X6)
% 0.82/1.03          | ~ (v1_relat_1 @ X6))),
% 0.82/1.03      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.82/1.03  thf('29', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.82/1.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.82/1.03  thf('30', plain,
% 0.82/1.03      (![X5 : $i, X6 : $i]:
% 0.82/1.03         (~ (v1_relat_1 @ X5)
% 0.82/1.03          | ~ (v1_funct_1 @ X5)
% 0.82/1.03          | ((X5) = (k2_funct_1 @ X6))
% 0.82/1.03          | ((k5_relat_1 @ X6 @ X5) != (k6_partfun1 @ (k1_relat_1 @ X6)))
% 0.82/1.03          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X5))
% 0.82/1.03          | ~ (v2_funct_1 @ X6)
% 0.82/1.03          | ~ (v1_funct_1 @ X6)
% 0.82/1.03          | ~ (v1_relat_1 @ X6))),
% 0.82/1.03      inference('demod', [status(thm)], ['28', '29'])).
% 0.82/1.03  thf('31', plain,
% 0.82/1.03      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.82/1.03        | ~ (v1_relat_1 @ sk_C)
% 0.82/1.03        | ~ (v1_funct_1 @ sk_C)
% 0.82/1.03        | ~ (v2_funct_1 @ sk_C)
% 0.82/1.03        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.82/1.03        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.82/1.03        | ~ (v1_funct_1 @ sk_D)
% 0.82/1.03        | ~ (v1_relat_1 @ sk_D))),
% 0.82/1.03      inference('sup-', [status(thm)], ['27', '30'])).
% 0.82/1.03  thf('32', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(d1_funct_2, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.03       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.82/1.03           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.82/1.03             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.82/1.03         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.82/1.03           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.82/1.03             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.82/1.03  thf(zf_stmt_1, axiom,
% 0.82/1.03    (![C:$i,B:$i,A:$i]:
% 0.82/1.03     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.82/1.03       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.82/1.03  thf('33', plain,
% 0.82/1.03      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.82/1.03         (~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.82/1.03          | ((X17) = (k1_relset_1 @ X17 @ X18 @ X19))
% 0.82/1.03          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.82/1.03  thf('34', plain,
% 0.82/1.03      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.82/1.03        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['32', '33'])).
% 0.82/1.03  thf(zf_stmt_2, axiom,
% 0.82/1.03    (![B:$i,A:$i]:
% 0.82/1.03     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.82/1.03       ( zip_tseitin_0 @ B @ A ) ))).
% 0.82/1.03  thf('35', plain,
% 0.82/1.03      (![X15 : $i, X16 : $i]:
% 0.82/1.03         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.03  thf('36', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.82/1.03  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.82/1.03  thf(zf_stmt_5, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.03       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.82/1.03         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.82/1.03           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.82/1.03             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.82/1.03  thf('37', plain,
% 0.82/1.03      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.82/1.03         (~ (zip_tseitin_0 @ X20 @ X21)
% 0.82/1.03          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 0.82/1.03          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.82/1.03  thf('38', plain,
% 0.82/1.03      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.82/1.03      inference('sup-', [status(thm)], ['36', '37'])).
% 0.82/1.03  thf('39', plain,
% 0.82/1.03      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.82/1.03      inference('sup-', [status(thm)], ['35', '38'])).
% 0.82/1.03  thf('40', plain, (((sk_B) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('41', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.82/1.03      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.82/1.03  thf('42', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(redefinition_k1_relset_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.03       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.82/1.03  thf('43', plain,
% 0.82/1.03      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.82/1.03         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.82/1.03          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.82/1.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.82/1.03  thf('44', plain,
% 0.82/1.03      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.82/1.03      inference('sup-', [status(thm)], ['42', '43'])).
% 0.82/1.03  thf('45', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.82/1.03      inference('demod', [status(thm)], ['34', '41', '44'])).
% 0.82/1.03  thf('46', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(cc2_relat_1, axiom,
% 0.82/1.03    (![A:$i]:
% 0.82/1.03     ( ( v1_relat_1 @ A ) =>
% 0.82/1.03       ( ![B:$i]:
% 0.82/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.82/1.03  thf('47', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.82/1.03          | (v1_relat_1 @ X0)
% 0.82/1.03          | ~ (v1_relat_1 @ X1))),
% 0.82/1.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.82/1.03  thf('48', plain,
% 0.82/1.03      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.82/1.03      inference('sup-', [status(thm)], ['46', '47'])).
% 0.82/1.03  thf(fc6_relat_1, axiom,
% 0.82/1.03    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.82/1.03  thf('49', plain,
% 0.82/1.03      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.82/1.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.82/1.03  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.82/1.03      inference('demod', [status(thm)], ['48', '49'])).
% 0.82/1.03  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('52', plain, ((v2_funct_1 @ sk_C)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(t55_funct_1, axiom,
% 0.82/1.03    (![A:$i]:
% 0.82/1.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.82/1.03       ( ( v2_funct_1 @ A ) =>
% 0.82/1.03         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.82/1.03           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.82/1.03  thf('53', plain,
% 0.82/1.03      (![X4 : $i]:
% 0.82/1.03         (~ (v2_funct_1 @ X4)
% 0.82/1.03          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.82/1.03          | ~ (v1_funct_1 @ X4)
% 0.82/1.03          | ~ (v1_relat_1 @ X4))),
% 0.82/1.03      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.82/1.03  thf('54', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(t31_funct_2, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.82/1.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.03       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.82/1.03         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.82/1.03           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.82/1.03           ( m1_subset_1 @
% 0.82/1.03             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.82/1.03  thf('55', plain,
% 0.82/1.03      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.82/1.03         (~ (v2_funct_1 @ X36)
% 0.82/1.03          | ((k2_relset_1 @ X38 @ X37 @ X36) != (X37))
% 0.82/1.03          | (m1_subset_1 @ (k2_funct_1 @ X36) @ 
% 0.82/1.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.82/1.03          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.82/1.03          | ~ (v1_funct_2 @ X36 @ X38 @ X37)
% 0.82/1.03          | ~ (v1_funct_1 @ X36))),
% 0.82/1.03      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.82/1.03  thf('56', plain,
% 0.82/1.03      ((~ (v1_funct_1 @ sk_C)
% 0.82/1.03        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.82/1.03        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.82/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.82/1.03        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.82/1.03        | ~ (v2_funct_1 @ sk_C))),
% 0.82/1.03      inference('sup-', [status(thm)], ['54', '55'])).
% 0.82/1.03  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('58', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('59', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('60', plain, ((v2_funct_1 @ sk_C)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('61', plain,
% 0.82/1.03      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.82/1.03         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.82/1.03        | ((sk_B) != (sk_B)))),
% 0.82/1.03      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 0.82/1.03  thf('62', plain,
% 0.82/1.03      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.82/1.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.82/1.03      inference('simplify', [status(thm)], ['61'])).
% 0.82/1.03  thf('63', plain,
% 0.82/1.03      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.82/1.03         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.82/1.03          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.82/1.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.82/1.03  thf('64', plain,
% 0.82/1.03      (((k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C))
% 0.82/1.03         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['62', '63'])).
% 0.82/1.03  thf('65', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('66', plain,
% 0.82/1.03      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.82/1.03         (~ (v2_funct_1 @ X36)
% 0.82/1.03          | ((k2_relset_1 @ X38 @ X37 @ X36) != (X37))
% 0.82/1.03          | (v1_funct_2 @ (k2_funct_1 @ X36) @ X37 @ X38)
% 0.82/1.03          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.82/1.03          | ~ (v1_funct_2 @ X36 @ X38 @ X37)
% 0.82/1.03          | ~ (v1_funct_1 @ X36))),
% 0.82/1.03      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.82/1.03  thf('67', plain,
% 0.82/1.03      ((~ (v1_funct_1 @ sk_C)
% 0.82/1.03        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.82/1.03        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.82/1.03        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.82/1.03        | ~ (v2_funct_1 @ sk_C))),
% 0.82/1.03      inference('sup-', [status(thm)], ['65', '66'])).
% 0.82/1.03  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('69', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('70', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('71', plain, ((v2_funct_1 @ sk_C)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('72', plain,
% 0.82/1.03      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.82/1.03      inference('demod', [status(thm)], ['67', '68', '69', '70', '71'])).
% 0.82/1.03  thf('73', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.82/1.03      inference('simplify', [status(thm)], ['72'])).
% 0.82/1.03  thf('74', plain,
% 0.82/1.03      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.82/1.03         (~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.82/1.03          | ((X17) = (k1_relset_1 @ X17 @ X18 @ X19))
% 0.82/1.03          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.82/1.03  thf('75', plain,
% 0.82/1.03      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)
% 0.82/1.03        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C))))),
% 0.82/1.03      inference('sup-', [status(thm)], ['73', '74'])).
% 0.82/1.03  thf('76', plain,
% 0.82/1.03      (![X15 : $i, X16 : $i]:
% 0.82/1.03         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.03  thf('77', plain,
% 0.82/1.03      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.82/1.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.82/1.03      inference('simplify', [status(thm)], ['61'])).
% 0.82/1.03  thf('78', plain,
% 0.82/1.03      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.82/1.03         (~ (zip_tseitin_0 @ X20 @ X21)
% 0.82/1.03          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 0.82/1.03          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.82/1.03  thf('79', plain,
% 0.82/1.03      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)
% 0.82/1.03        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.82/1.03      inference('sup-', [status(thm)], ['77', '78'])).
% 0.82/1.03  thf('80', plain,
% 0.82/1.03      ((((sk_A) = (k1_xboole_0))
% 0.82/1.03        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B))),
% 0.82/1.03      inference('sup-', [status(thm)], ['76', '79'])).
% 0.82/1.03  thf('81', plain, (((sk_A) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('82', plain, ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)),
% 0.82/1.03      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.82/1.03  thf('83', plain,
% 0.82/1.03      (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)))),
% 0.82/1.03      inference('demod', [status(thm)], ['75', '82'])).
% 0.82/1.03  thf('84', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.82/1.03      inference('sup+', [status(thm)], ['64', '83'])).
% 0.82/1.03  thf('85', plain,
% 0.82/1.03      ((((sk_B) = (k2_relat_1 @ sk_C))
% 0.82/1.03        | ~ (v1_relat_1 @ sk_C)
% 0.82/1.03        | ~ (v1_funct_1 @ sk_C)
% 0.82/1.03        | ~ (v2_funct_1 @ sk_C))),
% 0.82/1.03      inference('sup+', [status(thm)], ['53', '84'])).
% 0.82/1.03  thf('86', plain, ((v1_relat_1 @ sk_C)),
% 0.82/1.03      inference('demod', [status(thm)], ['48', '49'])).
% 0.82/1.03  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('89', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.82/1.03      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.82/1.03  thf('90', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('91', plain,
% 0.82/1.03      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.82/1.03         (~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.82/1.03          | ((X17) = (k1_relset_1 @ X17 @ X18 @ X19))
% 0.82/1.03          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.82/1.03  thf('92', plain,
% 0.82/1.03      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.82/1.03        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['90', '91'])).
% 0.82/1.03  thf('93', plain,
% 0.82/1.03      (![X15 : $i, X16 : $i]:
% 0.82/1.03         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.03  thf('94', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('95', plain,
% 0.82/1.03      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.82/1.03         (~ (zip_tseitin_0 @ X20 @ X21)
% 0.82/1.03          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 0.82/1.03          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.82/1.03  thf('96', plain,
% 0.82/1.03      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.82/1.03      inference('sup-', [status(thm)], ['94', '95'])).
% 0.82/1.03  thf('97', plain,
% 0.82/1.03      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.82/1.03      inference('sup-', [status(thm)], ['93', '96'])).
% 0.82/1.03  thf('98', plain, (((sk_A) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('99', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.82/1.03      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 0.82/1.03  thf('100', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('101', plain,
% 0.82/1.03      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.82/1.03         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.82/1.03          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.82/1.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.82/1.03  thf('102', plain,
% 0.82/1.03      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.82/1.03      inference('sup-', [status(thm)], ['100', '101'])).
% 0.82/1.03  thf('103', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.82/1.03      inference('demod', [status(thm)], ['92', '99', '102'])).
% 0.82/1.03  thf('104', plain, ((v1_funct_1 @ sk_D)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('105', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('106', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.82/1.03          | (v1_relat_1 @ X0)
% 0.82/1.03          | ~ (v1_relat_1 @ X1))),
% 0.82/1.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.82/1.03  thf('107', plain,
% 0.82/1.03      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.82/1.03      inference('sup-', [status(thm)], ['105', '106'])).
% 0.82/1.03  thf('108', plain,
% 0.82/1.03      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.82/1.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.82/1.03  thf('109', plain, ((v1_relat_1 @ sk_D)),
% 0.82/1.03      inference('demod', [status(thm)], ['107', '108'])).
% 0.82/1.03  thf('110', plain,
% 0.82/1.03      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.82/1.03        | ((sk_B) != (sk_B))
% 0.82/1.03        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.82/1.03      inference('demod', [status(thm)],
% 0.82/1.03                ['31', '45', '50', '51', '52', '89', '103', '104', '109'])).
% 0.82/1.03  thf('111', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.82/1.03      inference('simplify', [status(thm)], ['110'])).
% 0.82/1.03  thf('112', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('113', plain, ($false),
% 0.82/1.03      inference('simplify_reflect-', [status(thm)], ['111', '112'])).
% 0.82/1.03  
% 0.82/1.03  % SZS output end Refutation
% 0.82/1.03  
% 0.82/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
