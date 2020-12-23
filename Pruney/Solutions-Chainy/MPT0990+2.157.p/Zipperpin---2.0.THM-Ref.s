%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sCYQAeOvNq

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:22 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 197 expanded)
%              Number of leaves         :   42 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          : 1068 (4294 expanded)
%              Number of equality atoms :   71 ( 308 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 )
        = ( k5_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('26',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

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

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k2_funct_1 @ X5 ) )
      | ( ( k5_relat_1 @ X5 @ X4 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('31',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('70',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['60','67','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('77',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ( sk_B != sk_B )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','45','50','51','52','57','71','72','77'])).

thf('79',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sCYQAeOvNq
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:06:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.57/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.79  % Solved by: fo/fo7.sh
% 0.57/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.79  % done 214 iterations in 0.290s
% 0.57/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.79  % SZS output start Refutation
% 0.57/0.79  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.57/0.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.57/0.79  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.57/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.57/0.79  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.57/0.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.57/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.57/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.57/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.79  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.57/0.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.57/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.57/0.79  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.57/0.79  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.57/0.79  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.57/0.79  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.57/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.57/0.79  thf(sk_D_type, type, sk_D: $i).
% 0.57/0.79  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.57/0.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.57/0.79  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.57/0.79  thf(t36_funct_2, conjecture,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.57/0.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.57/0.79       ( ![D:$i]:
% 0.57/0.79         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.57/0.79             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.57/0.79           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.57/0.79               ( r2_relset_1 @
% 0.57/0.79                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.57/0.79                 ( k6_partfun1 @ A ) ) & 
% 0.57/0.79               ( v2_funct_1 @ C ) ) =>
% 0.57/0.79             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.57/0.79               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.57/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.79    (~( ![A:$i,B:$i,C:$i]:
% 0.57/0.79        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.57/0.79            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.57/0.79          ( ![D:$i]:
% 0.57/0.79            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.57/0.79                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.57/0.79              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.57/0.79                  ( r2_relset_1 @
% 0.57/0.79                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.57/0.79                    ( k6_partfun1 @ A ) ) & 
% 0.57/0.79                  ( v2_funct_1 @ C ) ) =>
% 0.57/0.79                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.57/0.79                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.57/0.79    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.57/0.79  thf('0', plain,
% 0.57/0.79      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.57/0.79        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.57/0.79        (k6_partfun1 @ sk_A))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(redefinition_k6_partfun1, axiom,
% 0.57/0.79    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.57/0.79  thf('1', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.57/0.79      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.57/0.79  thf('2', plain,
% 0.57/0.79      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.57/0.79        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.57/0.79        (k6_relat_1 @ sk_A))),
% 0.57/0.79      inference('demod', [status(thm)], ['0', '1'])).
% 0.57/0.79  thf('3', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('4', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(redefinition_k1_partfun1, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.57/0.79     ( ( ( v1_funct_1 @ E ) & 
% 0.57/0.79         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.57/0.79         ( v1_funct_1 @ F ) & 
% 0.57/0.79         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.57/0.79       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.57/0.79  thf('5', plain,
% 0.57/0.79      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.57/0.79         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.57/0.79          | ~ (v1_funct_1 @ X32)
% 0.57/0.79          | ~ (v1_funct_1 @ X35)
% 0.57/0.79          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.57/0.79          | ((k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 0.57/0.79              = (k5_relat_1 @ X32 @ X35)))),
% 0.57/0.79      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.57/0.79  thf('6', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.79         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.57/0.79            = (k5_relat_1 @ sk_C @ X0))
% 0.57/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.57/0.79          | ~ (v1_funct_1 @ X0)
% 0.57/0.79          | ~ (v1_funct_1 @ sk_C))),
% 0.57/0.79      inference('sup-', [status(thm)], ['4', '5'])).
% 0.57/0.79  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('8', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.79         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.57/0.79            = (k5_relat_1 @ sk_C @ X0))
% 0.57/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.57/0.79          | ~ (v1_funct_1 @ X0))),
% 0.57/0.79      inference('demod', [status(thm)], ['6', '7'])).
% 0.57/0.79  thf('9', plain,
% 0.57/0.79      ((~ (v1_funct_1 @ sk_D)
% 0.57/0.79        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.57/0.79            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['3', '8'])).
% 0.57/0.79  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('11', plain,
% 0.57/0.79      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.57/0.79         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.57/0.79      inference('demod', [status(thm)], ['9', '10'])).
% 0.57/0.79  thf('12', plain,
% 0.57/0.79      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.57/0.79        (k6_relat_1 @ sk_A))),
% 0.57/0.79      inference('demod', [status(thm)], ['2', '11'])).
% 0.57/0.79  thf('13', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('14', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(dt_k1_partfun1, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.57/0.79     ( ( ( v1_funct_1 @ E ) & 
% 0.57/0.79         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.57/0.79         ( v1_funct_1 @ F ) & 
% 0.57/0.79         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.57/0.79       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.57/0.79         ( m1_subset_1 @
% 0.57/0.79           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.57/0.79           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.57/0.79  thf('15', plain,
% 0.57/0.79      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.57/0.79         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.57/0.79          | ~ (v1_funct_1 @ X24)
% 0.57/0.79          | ~ (v1_funct_1 @ X27)
% 0.57/0.79          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.57/0.79          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 0.57/0.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 0.57/0.79      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.57/0.79  thf('16', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.79         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.57/0.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.57/0.79          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.57/0.79          | ~ (v1_funct_1 @ X1)
% 0.57/0.79          | ~ (v1_funct_1 @ sk_C))),
% 0.57/0.79      inference('sup-', [status(thm)], ['14', '15'])).
% 0.57/0.79  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('18', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.79         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.57/0.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.57/0.79          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.57/0.79          | ~ (v1_funct_1 @ X1))),
% 0.57/0.79      inference('demod', [status(thm)], ['16', '17'])).
% 0.57/0.79  thf('19', plain,
% 0.57/0.79      ((~ (v1_funct_1 @ sk_D)
% 0.57/0.79        | (m1_subset_1 @ 
% 0.57/0.79           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.57/0.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.57/0.79      inference('sup-', [status(thm)], ['13', '18'])).
% 0.57/0.79  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('21', plain,
% 0.57/0.79      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.57/0.79         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.57/0.79      inference('demod', [status(thm)], ['9', '10'])).
% 0.57/0.79  thf('22', plain,
% 0.57/0.79      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.57/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.57/0.79      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.57/0.79  thf(redefinition_r2_relset_1, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.79     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.57/0.79         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.57/0.79       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.57/0.79  thf('23', plain,
% 0.57/0.79      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.57/0.79         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.57/0.79          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.57/0.79          | ((X12) = (X15))
% 0.57/0.79          | ~ (r2_relset_1 @ X13 @ X14 @ X12 @ X15))),
% 0.57/0.79      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.57/0.79  thf('24', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.57/0.79          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.57/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.57/0.79      inference('sup-', [status(thm)], ['22', '23'])).
% 0.57/0.79  thf('25', plain,
% 0.57/0.79      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.57/0.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.57/0.79        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['12', '24'])).
% 0.57/0.79  thf(dt_k6_partfun1, axiom,
% 0.57/0.79    (![A:$i]:
% 0.57/0.79     ( ( m1_subset_1 @
% 0.57/0.79         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.57/0.79       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.57/0.79  thf('26', plain,
% 0.57/0.79      (![X31 : $i]:
% 0.57/0.79         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 0.57/0.79          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.57/0.79      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.57/0.79  thf('27', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.57/0.79      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.57/0.79  thf('28', plain,
% 0.57/0.79      (![X31 : $i]:
% 0.57/0.79         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 0.57/0.79          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.57/0.79      inference('demod', [status(thm)], ['26', '27'])).
% 0.57/0.79  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.57/0.79      inference('demod', [status(thm)], ['25', '28'])).
% 0.57/0.79  thf(t63_funct_1, axiom,
% 0.57/0.79    (![A:$i]:
% 0.57/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.57/0.79       ( ![B:$i]:
% 0.57/0.79         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.57/0.79           ( ( ( v2_funct_1 @ A ) & 
% 0.57/0.79               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.57/0.79               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.57/0.79             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.57/0.79  thf('30', plain,
% 0.57/0.79      (![X4 : $i, X5 : $i]:
% 0.57/0.79         (~ (v1_relat_1 @ X4)
% 0.57/0.79          | ~ (v1_funct_1 @ X4)
% 0.57/0.79          | ((X4) = (k2_funct_1 @ X5))
% 0.57/0.79          | ((k5_relat_1 @ X5 @ X4) != (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.57/0.79          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X4))
% 0.57/0.79          | ~ (v2_funct_1 @ X5)
% 0.57/0.79          | ~ (v1_funct_1 @ X5)
% 0.57/0.79          | ~ (v1_relat_1 @ X5))),
% 0.57/0.79      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.57/0.79  thf('31', plain,
% 0.57/0.79      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 0.57/0.79        | ~ (v1_relat_1 @ sk_C)
% 0.57/0.79        | ~ (v1_funct_1 @ sk_C)
% 0.57/0.79        | ~ (v2_funct_1 @ sk_C)
% 0.57/0.79        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.57/0.79        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.57/0.79        | ~ (v1_funct_1 @ sk_D)
% 0.57/0.79        | ~ (v1_relat_1 @ sk_D))),
% 0.57/0.79      inference('sup-', [status(thm)], ['29', '30'])).
% 0.57/0.79  thf('32', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(d1_funct_2, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.79       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.57/0.79           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.57/0.79             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.57/0.79         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.57/0.79           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.57/0.79             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.57/0.79  thf(zf_stmt_1, axiom,
% 0.57/0.79    (![C:$i,B:$i,A:$i]:
% 0.57/0.79     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.57/0.79       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.57/0.79  thf('33', plain,
% 0.57/0.79      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.57/0.79         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.57/0.79          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.57/0.79          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.57/0.79  thf('34', plain,
% 0.57/0.79      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.57/0.79        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['32', '33'])).
% 0.57/0.79  thf(zf_stmt_2, axiom,
% 0.57/0.79    (![B:$i,A:$i]:
% 0.57/0.79     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.57/0.79       ( zip_tseitin_0 @ B @ A ) ))).
% 0.57/0.79  thf('35', plain,
% 0.57/0.79      (![X16 : $i, X17 : $i]:
% 0.57/0.79         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.57/0.79  thf('36', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.57/0.79  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.57/0.79  thf(zf_stmt_5, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.79       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.57/0.79         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.57/0.79           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.57/0.79             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.57/0.79  thf('37', plain,
% 0.57/0.79      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.57/0.79         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.57/0.79          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.57/0.79          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.57/0.79  thf('38', plain,
% 0.57/0.79      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.57/0.79      inference('sup-', [status(thm)], ['36', '37'])).
% 0.57/0.79  thf('39', plain,
% 0.57/0.79      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.57/0.79      inference('sup-', [status(thm)], ['35', '38'])).
% 0.57/0.79  thf('40', plain, (((sk_B) != (k1_xboole_0))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('41', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.57/0.79      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.57/0.79  thf('42', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(redefinition_k1_relset_1, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.79       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.57/0.79  thf('43', plain,
% 0.57/0.79      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.57/0.79         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.57/0.79          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.57/0.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.57/0.79  thf('44', plain,
% 0.57/0.79      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.57/0.79      inference('sup-', [status(thm)], ['42', '43'])).
% 0.57/0.79  thf('45', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.57/0.79      inference('demod', [status(thm)], ['34', '41', '44'])).
% 0.57/0.79  thf('46', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(cc2_relat_1, axiom,
% 0.57/0.79    (![A:$i]:
% 0.57/0.79     ( ( v1_relat_1 @ A ) =>
% 0.57/0.79       ( ![B:$i]:
% 0.57/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.57/0.79  thf('47', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.57/0.79          | (v1_relat_1 @ X0)
% 0.57/0.79          | ~ (v1_relat_1 @ X1))),
% 0.57/0.79      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.57/0.79  thf('48', plain,
% 0.57/0.79      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.57/0.79      inference('sup-', [status(thm)], ['46', '47'])).
% 0.57/0.79  thf(fc6_relat_1, axiom,
% 0.57/0.79    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.57/0.79  thf('49', plain,
% 0.57/0.79      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.57/0.79      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.57/0.79  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.57/0.79      inference('demod', [status(thm)], ['48', '49'])).
% 0.57/0.79  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('52', plain, ((v2_funct_1 @ sk_C)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('53', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(redefinition_k2_relset_1, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.79       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.57/0.79  thf('54', plain,
% 0.57/0.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.57/0.79         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.57/0.79          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.57/0.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.57/0.79  thf('55', plain,
% 0.57/0.79      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.57/0.79      inference('sup-', [status(thm)], ['53', '54'])).
% 0.57/0.79  thf('56', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('57', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.57/0.79      inference('sup+', [status(thm)], ['55', '56'])).
% 0.57/0.79  thf('58', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('59', plain,
% 0.57/0.79      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.57/0.79         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.57/0.79          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.57/0.79          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.57/0.79  thf('60', plain,
% 0.57/0.79      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.57/0.79        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['58', '59'])).
% 0.57/0.79  thf('61', plain,
% 0.57/0.79      (![X16 : $i, X17 : $i]:
% 0.57/0.79         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.57/0.79  thf('62', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('63', plain,
% 0.57/0.79      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.57/0.79         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.57/0.79          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.57/0.79          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.57/0.79  thf('64', plain,
% 0.57/0.79      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.57/0.79      inference('sup-', [status(thm)], ['62', '63'])).
% 0.57/0.79  thf('65', plain,
% 0.57/0.79      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.57/0.79      inference('sup-', [status(thm)], ['61', '64'])).
% 0.57/0.79  thf('66', plain, (((sk_A) != (k1_xboole_0))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('67', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.57/0.79      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.57/0.79  thf('68', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('69', plain,
% 0.57/0.79      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.57/0.79         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.57/0.79          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.57/0.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.57/0.79  thf('70', plain,
% 0.57/0.79      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.57/0.79      inference('sup-', [status(thm)], ['68', '69'])).
% 0.57/0.79  thf('71', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.57/0.79      inference('demod', [status(thm)], ['60', '67', '70'])).
% 0.57/0.79  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('73', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('74', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.57/0.79          | (v1_relat_1 @ X0)
% 0.57/0.79          | ~ (v1_relat_1 @ X1))),
% 0.57/0.79      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.57/0.79  thf('75', plain,
% 0.57/0.79      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.57/0.79      inference('sup-', [status(thm)], ['73', '74'])).
% 0.57/0.79  thf('76', plain,
% 0.57/0.79      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.57/0.79      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.57/0.79  thf('77', plain, ((v1_relat_1 @ sk_D)),
% 0.57/0.79      inference('demod', [status(thm)], ['75', '76'])).
% 0.57/0.79  thf('78', plain,
% 0.57/0.79      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 0.57/0.79        | ((sk_B) != (sk_B))
% 0.57/0.79        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.57/0.79      inference('demod', [status(thm)],
% 0.57/0.79                ['31', '45', '50', '51', '52', '57', '71', '72', '77'])).
% 0.57/0.79  thf('79', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.57/0.79      inference('simplify', [status(thm)], ['78'])).
% 0.57/0.79  thf('80', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('81', plain, ($false),
% 0.57/0.79      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 0.57/0.79  
% 0.57/0.79  % SZS output end Refutation
% 0.57/0.79  
% 0.57/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
