%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6d6qsqH4li

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:26 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 590 expanded)
%              Number of leaves         :   48 ( 194 expanded)
%              Depth                    :   24
%              Number of atoms          : 1876 (14123 expanded)
%              Number of equality atoms :  109 ( 904 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

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

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ X50 @ ( k2_funct_1 @ X50 ) )
        = ( k6_partfun1 @ X51 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ X50 @ ( k2_funct_1 @ X50 ) )
        = ( k6_relat_1 @ X51 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('24',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('25',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('29',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_relset_1 @ X37 @ X37 @ ( k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39 ) @ ( k6_partfun1 @ X37 ) )
      | ( ( k2_relset_1 @ X38 @ X37 @ X39 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('30',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_relset_1 @ X37 @ X37 @ ( k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39 ) @ ( k6_relat_1 @ X37 ) )
      | ( ( k2_relset_1 @ X38 @ X37 @ X39 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('38',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('39',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['36','40','41','42','43','44'])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['8','45'])).

thf('47',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','46','47','48'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ! [E: $i] :
          ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
            & ( v1_funct_2 @ E @ B @ C )
            & ( v1_funct_1 @ E ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) )
           => ( ( ( v2_funct_1 @ E )
                & ( v2_funct_1 @ D ) )
              | ( ( B != k1_xboole_0 )
                & ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i] :
      ( ( zip_tseitin_1 @ C @ B )
     => ( ( C = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [E: $i,D: $i] :
      ( ( zip_tseitin_0 @ E @ D )
     => ( ( v2_funct_1 @ D )
        & ( v2_funct_1 @ E ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
              & ( ( k2_relset_1 @ A @ B @ D )
                = B ) )
           => ( ( zip_tseitin_1 @ C @ B )
              | ( zip_tseitin_0 @ E @ D ) ) ) ) ) )).

thf('55',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( zip_tseitin_0 @ X44 @ X47 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X48 @ X45 @ X45 @ X46 @ X47 @ X44 ) )
      | ( zip_tseitin_1 @ X46 @ X45 )
      | ( ( k2_relset_1 @ X48 @ X45 @ X47 )
       != X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X45 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('61',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('62',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['60','61','62','63','64','65'])).

thf('67',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('69',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v2_funct_1 @ X41 )
      | ~ ( zip_tseitin_0 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('73',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['52','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
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

thf('77',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('84',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('85',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('90',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('96',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','91','96'])).

thf('98',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['74','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('101',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['101','102'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('104',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('105',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['89','90'])).

thf('107',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['98','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['36','40','41','42','43','44'])).

thf('110',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('111',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('112',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['109','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['94','95'])).

thf('118',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('121',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['108','121'])).

thf('123',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C ) ),
    inference('sup-',[status(thm)],['0','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['94','95'])).

thf('125',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k2_funct_1 @ sk_D )
    = sk_C ),
    inference(demod,[status(thm)],['123','124','125'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('127',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('128',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['94','95'])).

thf('130',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('132',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['132','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6d6qsqH4li
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:35:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 2.04/2.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.04/2.24  % Solved by: fo/fo7.sh
% 2.04/2.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.04/2.24  % done 1641 iterations in 1.782s
% 2.04/2.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.04/2.24  % SZS output start Refutation
% 2.04/2.24  thf(sk_B_type, type, sk_B: $i).
% 2.04/2.24  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.04/2.24  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.04/2.24  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.04/2.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.04/2.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.04/2.24  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.04/2.24  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.04/2.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.04/2.24  thf(sk_D_type, type, sk_D: $i).
% 2.04/2.24  thf(sk_A_type, type, sk_A: $i).
% 2.04/2.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.04/2.24  thf(sk_C_type, type, sk_C: $i).
% 2.04/2.24  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.04/2.24  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.04/2.24  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.04/2.24  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.04/2.24  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.04/2.24  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 2.04/2.24  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.04/2.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.04/2.24  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.04/2.24  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.04/2.24  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.04/2.24  thf(dt_k2_funct_1, axiom,
% 2.04/2.24    (![A:$i]:
% 2.04/2.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.04/2.24       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.04/2.24         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.04/2.24  thf('0', plain,
% 2.04/2.24      (![X9 : $i]:
% 2.04/2.24         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 2.04/2.24          | ~ (v1_funct_1 @ X9)
% 2.04/2.24          | ~ (v1_relat_1 @ X9))),
% 2.04/2.24      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.04/2.24  thf(t36_funct_2, conjecture,
% 2.04/2.24    (![A:$i,B:$i,C:$i]:
% 2.04/2.24     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.04/2.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.04/2.24       ( ![D:$i]:
% 2.04/2.24         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.04/2.24             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.04/2.24           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.04/2.24               ( r2_relset_1 @
% 2.04/2.24                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.04/2.24                 ( k6_partfun1 @ A ) ) & 
% 2.04/2.24               ( v2_funct_1 @ C ) ) =>
% 2.04/2.24             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.04/2.24               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.04/2.24  thf(zf_stmt_0, negated_conjecture,
% 2.04/2.24    (~( ![A:$i,B:$i,C:$i]:
% 2.04/2.24        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.04/2.24            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.04/2.24          ( ![D:$i]:
% 2.04/2.24            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.04/2.24                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.04/2.24              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.04/2.24                  ( r2_relset_1 @
% 2.04/2.24                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.04/2.24                    ( k6_partfun1 @ A ) ) & 
% 2.04/2.24                  ( v2_funct_1 @ C ) ) =>
% 2.04/2.24                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.04/2.24                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.04/2.24    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.04/2.24  thf('1', plain,
% 2.04/2.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.04/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.24  thf(t35_funct_2, axiom,
% 2.04/2.24    (![A:$i,B:$i,C:$i]:
% 2.04/2.24     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.04/2.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.04/2.24       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.04/2.24         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.04/2.24           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 2.04/2.24             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 2.04/2.24  thf('2', plain,
% 2.04/2.24      (![X49 : $i, X50 : $i, X51 : $i]:
% 2.04/2.24         (((X49) = (k1_xboole_0))
% 2.04/2.24          | ~ (v1_funct_1 @ X50)
% 2.04/2.24          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 2.04/2.24          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 2.04/2.24          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_partfun1 @ X51))
% 2.04/2.24          | ~ (v2_funct_1 @ X50)
% 2.04/2.24          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 2.04/2.24      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.04/2.24  thf(redefinition_k6_partfun1, axiom,
% 2.04/2.24    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.04/2.24  thf('3', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 2.04/2.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.04/2.24  thf('4', plain,
% 2.04/2.24      (![X49 : $i, X50 : $i, X51 : $i]:
% 2.04/2.24         (((X49) = (k1_xboole_0))
% 2.04/2.24          | ~ (v1_funct_1 @ X50)
% 2.04/2.24          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 2.04/2.24          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 2.04/2.24          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_relat_1 @ X51))
% 2.04/2.24          | ~ (v2_funct_1 @ X50)
% 2.04/2.24          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 2.04/2.24      inference('demod', [status(thm)], ['2', '3'])).
% 2.04/2.24  thf('5', plain,
% 2.04/2.24      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 2.04/2.24        | ~ (v2_funct_1 @ sk_D)
% 2.04/2.24        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.04/2.24        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.04/2.24        | ~ (v1_funct_1 @ sk_D)
% 2.04/2.24        | ((sk_A) = (k1_xboole_0)))),
% 2.04/2.24      inference('sup-', [status(thm)], ['1', '4'])).
% 2.04/2.24  thf('6', plain,
% 2.04/2.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.04/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.24  thf(redefinition_k2_relset_1, axiom,
% 2.04/2.24    (![A:$i,B:$i,C:$i]:
% 2.04/2.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.04/2.24       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.04/2.24  thf('7', plain,
% 2.04/2.24      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.04/2.24         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 2.04/2.24          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.04/2.24      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.04/2.24  thf('8', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.04/2.24      inference('sup-', [status(thm)], ['6', '7'])).
% 2.04/2.24  thf('9', plain,
% 2.04/2.24      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.04/2.24        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.04/2.24        (k6_partfun1 @ sk_A))),
% 2.04/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.24  thf('10', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 2.04/2.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.04/2.24  thf('11', plain,
% 2.04/2.24      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.04/2.24        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.04/2.24        (k6_relat_1 @ sk_A))),
% 2.04/2.24      inference('demod', [status(thm)], ['9', '10'])).
% 2.04/2.24  thf('12', plain,
% 2.04/2.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.04/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.24  thf('13', plain,
% 2.04/2.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.04/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.24  thf(dt_k1_partfun1, axiom,
% 2.04/2.24    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.04/2.24     ( ( ( v1_funct_1 @ E ) & 
% 2.04/2.24         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.04/2.24         ( v1_funct_1 @ F ) & 
% 2.04/2.24         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.04/2.24       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.04/2.24         ( m1_subset_1 @
% 2.04/2.24           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.04/2.24           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.04/2.24  thf('14', plain,
% 2.04/2.24      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 2.04/2.24         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 2.04/2.24          | ~ (v1_funct_1 @ X21)
% 2.04/2.24          | ~ (v1_funct_1 @ X24)
% 2.04/2.24          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 2.04/2.24          | (m1_subset_1 @ (k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24) @ 
% 2.04/2.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X26))))),
% 2.04/2.24      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.04/2.24  thf('15', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.24         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.04/2.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.04/2.24          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.04/2.24          | ~ (v1_funct_1 @ X1)
% 2.04/2.24          | ~ (v1_funct_1 @ sk_C))),
% 2.04/2.24      inference('sup-', [status(thm)], ['13', '14'])).
% 2.04/2.24  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 2.04/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.24  thf('17', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.24         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.04/2.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.04/2.24          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.04/2.24          | ~ (v1_funct_1 @ X1))),
% 2.04/2.24      inference('demod', [status(thm)], ['15', '16'])).
% 2.04/2.24  thf('18', plain,
% 2.04/2.24      ((~ (v1_funct_1 @ sk_D)
% 2.04/2.24        | (m1_subset_1 @ 
% 2.04/2.24           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.04/2.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.04/2.24      inference('sup-', [status(thm)], ['12', '17'])).
% 2.04/2.24  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 2.04/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.24  thf('20', plain,
% 2.04/2.24      ((m1_subset_1 @ 
% 2.04/2.24        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.04/2.24        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.04/2.24      inference('demod', [status(thm)], ['18', '19'])).
% 2.04/2.24  thf(redefinition_r2_relset_1, axiom,
% 2.04/2.24    (![A:$i,B:$i,C:$i,D:$i]:
% 2.04/2.24     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.04/2.24         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.04/2.24       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.04/2.24  thf('21', plain,
% 2.04/2.24      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 2.04/2.24         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 2.04/2.24          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 2.04/2.24          | ((X17) = (X20))
% 2.04/2.24          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 2.04/2.24      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.04/2.24  thf('22', plain,
% 2.04/2.24      (![X0 : $i]:
% 2.04/2.24         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.04/2.24             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.04/2.24          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.04/2.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.04/2.24      inference('sup-', [status(thm)], ['20', '21'])).
% 2.04/2.24  thf('23', plain,
% 2.04/2.24      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.04/2.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.04/2.24        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.04/2.24            = (k6_relat_1 @ sk_A)))),
% 2.04/2.24      inference('sup-', [status(thm)], ['11', '22'])).
% 2.04/2.24  thf(dt_k6_partfun1, axiom,
% 2.04/2.24    (![A:$i]:
% 2.04/2.24     ( ( m1_subset_1 @
% 2.04/2.24         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.04/2.24       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.04/2.24  thf('24', plain,
% 2.04/2.24      (![X28 : $i]:
% 2.04/2.24         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 2.04/2.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 2.04/2.24      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.04/2.24  thf('25', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 2.04/2.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.04/2.24  thf('26', plain,
% 2.04/2.24      (![X28 : $i]:
% 2.04/2.24         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 2.04/2.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 2.04/2.24      inference('demod', [status(thm)], ['24', '25'])).
% 2.04/2.24  thf('27', plain,
% 2.04/2.24      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.04/2.24         = (k6_relat_1 @ sk_A))),
% 2.04/2.24      inference('demod', [status(thm)], ['23', '26'])).
% 2.04/2.24  thf('28', plain,
% 2.04/2.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.04/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.24  thf(t24_funct_2, axiom,
% 2.04/2.24    (![A:$i,B:$i,C:$i]:
% 2.04/2.24     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.04/2.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.04/2.24       ( ![D:$i]:
% 2.04/2.24         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.04/2.24             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.04/2.24           ( ( r2_relset_1 @
% 2.04/2.24               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.04/2.24               ( k6_partfun1 @ B ) ) =>
% 2.04/2.24             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.04/2.24  thf('29', plain,
% 2.04/2.24      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 2.04/2.24         (~ (v1_funct_1 @ X36)
% 2.04/2.24          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 2.04/2.24          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 2.04/2.24          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 2.04/2.24               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 2.04/2.24               (k6_partfun1 @ X37))
% 2.04/2.24          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 2.04/2.24          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 2.04/2.24          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 2.04/2.24          | ~ (v1_funct_1 @ X39))),
% 2.04/2.24      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.04/2.24  thf('30', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 2.04/2.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.04/2.24  thf('31', plain,
% 2.04/2.24      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 2.04/2.24         (~ (v1_funct_1 @ X36)
% 2.04/2.24          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 2.04/2.24          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 2.04/2.24          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 2.04/2.24               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 2.04/2.24               (k6_relat_1 @ X37))
% 2.04/2.24          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 2.04/2.24          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 2.04/2.24          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 2.04/2.24          | ~ (v1_funct_1 @ X39))),
% 2.04/2.24      inference('demod', [status(thm)], ['29', '30'])).
% 2.04/2.24  thf('32', plain,
% 2.04/2.24      (![X0 : $i]:
% 2.04/2.24         (~ (v1_funct_1 @ X0)
% 2.04/2.24          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.04/2.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.04/2.24          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.04/2.24          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.04/2.24               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.04/2.24               (k6_relat_1 @ sk_A))
% 2.04/2.24          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.04/2.24          | ~ (v1_funct_1 @ sk_C))),
% 2.04/2.24      inference('sup-', [status(thm)], ['28', '31'])).
% 2.04/2.24  thf('33', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.04/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.24  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 2.04/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.24  thf('35', plain,
% 2.04/2.24      (![X0 : $i]:
% 2.04/2.24         (~ (v1_funct_1 @ X0)
% 2.04/2.24          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.04/2.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.04/2.24          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.04/2.24          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.04/2.24               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.04/2.24               (k6_relat_1 @ sk_A)))),
% 2.04/2.24      inference('demod', [status(thm)], ['32', '33', '34'])).
% 2.04/2.24  thf('36', plain,
% 2.04/2.24      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 2.04/2.24           (k6_relat_1 @ sk_A))
% 2.04/2.24        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.04/2.24        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.04/2.24        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.04/2.24        | ~ (v1_funct_1 @ sk_D))),
% 2.04/2.24      inference('sup-', [status(thm)], ['27', '35'])).
% 2.04/2.24  thf('37', plain,
% 2.04/2.24      (![X28 : $i]:
% 2.04/2.24         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 2.04/2.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 2.04/2.24      inference('demod', [status(thm)], ['24', '25'])).
% 2.04/2.24  thf('38', plain,
% 2.04/2.24      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 2.04/2.24         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 2.04/2.24          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 2.04/2.24          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 2.04/2.24          | ((X17) != (X20)))),
% 2.04/2.24      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.04/2.24  thf('39', plain,
% 2.04/2.24      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.04/2.24         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 2.04/2.24          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 2.04/2.24      inference('simplify', [status(thm)], ['38'])).
% 2.04/2.24  thf('40', plain,
% 2.04/2.24      (![X0 : $i]:
% 2.04/2.24         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['37', '39'])).
% 2.04/2.24  thf('41', plain,
% 2.04/2.24      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.04/2.24      inference('sup-', [status(thm)], ['6', '7'])).
% 2.04/2.24  thf('42', plain,
% 2.04/2.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.04/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.24  thf('43', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.04/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.24  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('45', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.04/2.25      inference('demod', [status(thm)], ['36', '40', '41', '42', '43', '44'])).
% 2.04/2.25  thf('46', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 2.04/2.25      inference('demod', [status(thm)], ['8', '45'])).
% 2.04/2.25  thf('47', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('49', plain,
% 2.04/2.25      ((((sk_A) != (sk_A))
% 2.04/2.25        | ~ (v2_funct_1 @ sk_D)
% 2.04/2.25        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.04/2.25        | ((sk_A) = (k1_xboole_0)))),
% 2.04/2.25      inference('demod', [status(thm)], ['5', '46', '47', '48'])).
% 2.04/2.25  thf('50', plain,
% 2.04/2.25      ((((sk_A) = (k1_xboole_0))
% 2.04/2.25        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.04/2.25        | ~ (v2_funct_1 @ sk_D))),
% 2.04/2.25      inference('simplify', [status(thm)], ['49'])).
% 2.04/2.25  thf('51', plain, (((sk_A) != (k1_xboole_0))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('52', plain,
% 2.04/2.25      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.04/2.25        | ~ (v2_funct_1 @ sk_D))),
% 2.04/2.25      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 2.04/2.25  thf('53', plain,
% 2.04/2.25      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.04/2.25         = (k6_relat_1 @ sk_A))),
% 2.04/2.25      inference('demod', [status(thm)], ['23', '26'])).
% 2.04/2.25  thf('54', plain,
% 2.04/2.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf(t30_funct_2, axiom,
% 2.04/2.25    (![A:$i,B:$i,C:$i,D:$i]:
% 2.04/2.25     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.04/2.25         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 2.04/2.25       ( ![E:$i]:
% 2.04/2.25         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 2.04/2.25             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 2.04/2.25           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.04/2.25               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 2.04/2.25             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 2.04/2.25               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 2.04/2.25  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 2.04/2.25  thf(zf_stmt_2, axiom,
% 2.04/2.25    (![C:$i,B:$i]:
% 2.04/2.25     ( ( zip_tseitin_1 @ C @ B ) =>
% 2.04/2.25       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 2.04/2.25  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.04/2.25  thf(zf_stmt_4, axiom,
% 2.04/2.25    (![E:$i,D:$i]:
% 2.04/2.25     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 2.04/2.25  thf(zf_stmt_5, axiom,
% 2.04/2.25    (![A:$i,B:$i,C:$i,D:$i]:
% 2.04/2.25     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.04/2.25         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.04/2.25       ( ![E:$i]:
% 2.04/2.25         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.04/2.25             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.04/2.25           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 2.04/2.25               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 2.04/2.25             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 2.04/2.25  thf('55', plain,
% 2.04/2.25      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 2.04/2.25         (~ (v1_funct_1 @ X44)
% 2.04/2.25          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 2.04/2.25          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 2.04/2.25          | (zip_tseitin_0 @ X44 @ X47)
% 2.04/2.25          | ~ (v2_funct_1 @ (k1_partfun1 @ X48 @ X45 @ X45 @ X46 @ X47 @ X44))
% 2.04/2.25          | (zip_tseitin_1 @ X46 @ X45)
% 2.04/2.25          | ((k2_relset_1 @ X48 @ X45 @ X47) != (X45))
% 2.04/2.25          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X45)))
% 2.04/2.25          | ~ (v1_funct_2 @ X47 @ X48 @ X45)
% 2.04/2.25          | ~ (v1_funct_1 @ X47))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.04/2.25  thf('56', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (v1_funct_1 @ X0)
% 2.04/2.25          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.04/2.25          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.04/2.25          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.04/2.25          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.04/2.25          | (zip_tseitin_0 @ sk_D @ X0)
% 2.04/2.25          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.04/2.25          | ~ (v1_funct_1 @ sk_D))),
% 2.04/2.25      inference('sup-', [status(thm)], ['54', '55'])).
% 2.04/2.25  thf('57', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('58', plain, ((v1_funct_1 @ sk_D)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('59', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (v1_funct_1 @ X0)
% 2.04/2.25          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.04/2.25          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.04/2.25          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.04/2.25          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.04/2.25          | (zip_tseitin_0 @ sk_D @ X0))),
% 2.04/2.25      inference('demod', [status(thm)], ['56', '57', '58'])).
% 2.04/2.25  thf('60', plain,
% 2.04/2.25      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 2.04/2.25        | (zip_tseitin_0 @ sk_D @ sk_C)
% 2.04/2.25        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.04/2.25        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.04/2.25        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.04/2.25        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.04/2.25        | ~ (v1_funct_1 @ sk_C))),
% 2.04/2.25      inference('sup-', [status(thm)], ['53', '59'])).
% 2.04/2.25  thf(fc4_funct_1, axiom,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.04/2.25       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.04/2.25  thf('61', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 2.04/2.25      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.04/2.25  thf('62', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('63', plain,
% 2.04/2.25      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('64', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('66', plain,
% 2.04/2.25      (((zip_tseitin_0 @ sk_D @ sk_C)
% 2.04/2.25        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.04/2.25        | ((sk_B) != (sk_B)))),
% 2.04/2.25      inference('demod', [status(thm)], ['60', '61', '62', '63', '64', '65'])).
% 2.04/2.25  thf('67', plain,
% 2.04/2.25      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 2.04/2.25      inference('simplify', [status(thm)], ['66'])).
% 2.04/2.25  thf('68', plain,
% 2.04/2.25      (![X42 : $i, X43 : $i]:
% 2.04/2.25         (((X42) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X42 @ X43))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.04/2.25  thf('69', plain,
% 2.04/2.25      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['67', '68'])).
% 2.04/2.25  thf('70', plain, (((sk_A) != (k1_xboole_0))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('71', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 2.04/2.25      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 2.04/2.25  thf('72', plain,
% 2.04/2.25      (![X40 : $i, X41 : $i]:
% 2.04/2.25         ((v2_funct_1 @ X41) | ~ (zip_tseitin_0 @ X41 @ X40))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.04/2.25  thf('73', plain, ((v2_funct_1 @ sk_D)),
% 2.04/2.25      inference('sup-', [status(thm)], ['71', '72'])).
% 2.04/2.25  thf('74', plain,
% 2.04/2.25      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 2.04/2.25      inference('demod', [status(thm)], ['52', '73'])).
% 2.04/2.25  thf('75', plain,
% 2.04/2.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('76', plain,
% 2.04/2.25      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf(redefinition_k1_partfun1, axiom,
% 2.04/2.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.04/2.25     ( ( ( v1_funct_1 @ E ) & 
% 2.04/2.25         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.04/2.25         ( v1_funct_1 @ F ) & 
% 2.04/2.25         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.04/2.25       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.04/2.25  thf('77', plain,
% 2.04/2.25      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.04/2.25         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.04/2.25          | ~ (v1_funct_1 @ X29)
% 2.04/2.25          | ~ (v1_funct_1 @ X32)
% 2.04/2.25          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 2.04/2.25          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 2.04/2.25              = (k5_relat_1 @ X29 @ X32)))),
% 2.04/2.25      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.04/2.25  thf('78', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.25         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.04/2.25            = (k5_relat_1 @ sk_C @ X0))
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.04/2.25          | ~ (v1_funct_1 @ X0)
% 2.04/2.25          | ~ (v1_funct_1 @ sk_C))),
% 2.04/2.25      inference('sup-', [status(thm)], ['76', '77'])).
% 2.04/2.25  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('80', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.25         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.04/2.25            = (k5_relat_1 @ sk_C @ X0))
% 2.04/2.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.04/2.25          | ~ (v1_funct_1 @ X0))),
% 2.04/2.25      inference('demod', [status(thm)], ['78', '79'])).
% 2.04/2.25  thf('81', plain,
% 2.04/2.25      ((~ (v1_funct_1 @ sk_D)
% 2.04/2.25        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.04/2.25            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['75', '80'])).
% 2.04/2.25  thf('82', plain, ((v1_funct_1 @ sk_D)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('83', plain,
% 2.04/2.25      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.04/2.25         = (k6_relat_1 @ sk_A))),
% 2.04/2.25      inference('demod', [status(thm)], ['23', '26'])).
% 2.04/2.25  thf('84', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 2.04/2.25      inference('demod', [status(thm)], ['81', '82', '83'])).
% 2.04/2.25  thf(t55_relat_1, axiom,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( v1_relat_1 @ A ) =>
% 2.04/2.25       ( ![B:$i]:
% 2.04/2.25         ( ( v1_relat_1 @ B ) =>
% 2.04/2.25           ( ![C:$i]:
% 2.04/2.25             ( ( v1_relat_1 @ C ) =>
% 2.04/2.25               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.04/2.25                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.04/2.25  thf('85', plain,
% 2.04/2.25      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.04/2.25         (~ (v1_relat_1 @ X4)
% 2.04/2.25          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 2.04/2.25              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 2.04/2.25          | ~ (v1_relat_1 @ X6)
% 2.04/2.25          | ~ (v1_relat_1 @ X5))),
% 2.04/2.25      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.04/2.25  thf('86', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 2.04/2.25            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 2.04/2.25          | ~ (v1_relat_1 @ sk_C)
% 2.04/2.25          | ~ (v1_relat_1 @ X0)
% 2.04/2.25          | ~ (v1_relat_1 @ sk_D))),
% 2.04/2.25      inference('sup+', [status(thm)], ['84', '85'])).
% 2.04/2.25  thf('87', plain,
% 2.04/2.25      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf(cc2_relat_1, axiom,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( v1_relat_1 @ A ) =>
% 2.04/2.25       ( ![B:$i]:
% 2.04/2.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.04/2.25  thf('88', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.04/2.25          | (v1_relat_1 @ X0)
% 2.04/2.25          | ~ (v1_relat_1 @ X1))),
% 2.04/2.25      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.04/2.25  thf('89', plain,
% 2.04/2.25      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.04/2.25      inference('sup-', [status(thm)], ['87', '88'])).
% 2.04/2.25  thf(fc6_relat_1, axiom,
% 2.04/2.25    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.04/2.25  thf('90', plain,
% 2.04/2.25      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.04/2.25      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.04/2.25  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 2.04/2.25      inference('demod', [status(thm)], ['89', '90'])).
% 2.04/2.25  thf('92', plain,
% 2.04/2.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('93', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.04/2.25          | (v1_relat_1 @ X0)
% 2.04/2.25          | ~ (v1_relat_1 @ X1))),
% 2.04/2.25      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.04/2.25  thf('94', plain,
% 2.04/2.25      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.04/2.25      inference('sup-', [status(thm)], ['92', '93'])).
% 2.04/2.25  thf('95', plain,
% 2.04/2.25      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.04/2.25      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.04/2.25  thf('96', plain, ((v1_relat_1 @ sk_D)),
% 2.04/2.25      inference('demod', [status(thm)], ['94', '95'])).
% 2.04/2.25  thf('97', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 2.04/2.25            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 2.04/2.25          | ~ (v1_relat_1 @ X0))),
% 2.04/2.25      inference('demod', [status(thm)], ['86', '91', '96'])).
% 2.04/2.25  thf('98', plain,
% 2.04/2.25      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 2.04/2.25          = (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))
% 2.04/2.25        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 2.04/2.25      inference('sup+', [status(thm)], ['74', '97'])).
% 2.04/2.25  thf('99', plain,
% 2.04/2.25      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('100', plain,
% 2.04/2.25      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.04/2.25         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 2.04/2.25          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.04/2.25      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.04/2.25  thf('101', plain,
% 2.04/2.25      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.04/2.25      inference('sup-', [status(thm)], ['99', '100'])).
% 2.04/2.25  thf('102', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('103', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.04/2.25      inference('sup+', [status(thm)], ['101', '102'])).
% 2.04/2.25  thf(t80_relat_1, axiom,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( v1_relat_1 @ A ) =>
% 2.04/2.25       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.04/2.25  thf('104', plain,
% 2.04/2.25      (![X8 : $i]:
% 2.04/2.25         (((k5_relat_1 @ X8 @ (k6_relat_1 @ (k2_relat_1 @ X8))) = (X8))
% 2.04/2.25          | ~ (v1_relat_1 @ X8))),
% 2.04/2.25      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.04/2.25  thf('105', plain,
% 2.04/2.25      ((((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))
% 2.04/2.25        | ~ (v1_relat_1 @ sk_C))),
% 2.04/2.25      inference('sup+', [status(thm)], ['103', '104'])).
% 2.04/2.25  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 2.04/2.25      inference('demod', [status(thm)], ['89', '90'])).
% 2.04/2.25  thf('107', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 2.04/2.25      inference('demod', [status(thm)], ['105', '106'])).
% 2.04/2.25  thf('108', plain,
% 2.04/2.25      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k2_funct_1 @ sk_D)) = (sk_C))
% 2.04/2.25        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 2.04/2.25      inference('demod', [status(thm)], ['98', '107'])).
% 2.04/2.25  thf('109', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.04/2.25      inference('demod', [status(thm)], ['36', '40', '41', '42', '43', '44'])).
% 2.04/2.25  thf('110', plain,
% 2.04/2.25      (![X9 : $i]:
% 2.04/2.25         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 2.04/2.25          | ~ (v1_funct_1 @ X9)
% 2.04/2.25          | ~ (v1_relat_1 @ X9))),
% 2.04/2.25      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.04/2.25  thf(t55_funct_1, axiom,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.04/2.25       ( ( v2_funct_1 @ A ) =>
% 2.04/2.25         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.04/2.25           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.04/2.25  thf('111', plain,
% 2.04/2.25      (![X12 : $i]:
% 2.04/2.25         (~ (v2_funct_1 @ X12)
% 2.04/2.25          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 2.04/2.25          | ~ (v1_funct_1 @ X12)
% 2.04/2.25          | ~ (v1_relat_1 @ X12))),
% 2.04/2.25      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.04/2.25  thf(t78_relat_1, axiom,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( v1_relat_1 @ A ) =>
% 2.04/2.25       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 2.04/2.25  thf('112', plain,
% 2.04/2.25      (![X7 : $i]:
% 2.04/2.25         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X7)) @ X7) = (X7))
% 2.04/2.25          | ~ (v1_relat_1 @ X7))),
% 2.04/2.25      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.04/2.25  thf('113', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 2.04/2.25            = (k2_funct_1 @ X0))
% 2.04/2.25          | ~ (v1_relat_1 @ X0)
% 2.04/2.25          | ~ (v1_funct_1 @ X0)
% 2.04/2.25          | ~ (v2_funct_1 @ X0)
% 2.04/2.25          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.04/2.25      inference('sup+', [status(thm)], ['111', '112'])).
% 2.04/2.25  thf('114', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (~ (v1_relat_1 @ X0)
% 2.04/2.25          | ~ (v1_funct_1 @ X0)
% 2.04/2.25          | ~ (v2_funct_1 @ X0)
% 2.04/2.25          | ~ (v1_funct_1 @ X0)
% 2.04/2.25          | ~ (v1_relat_1 @ X0)
% 2.04/2.25          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 2.04/2.25              = (k2_funct_1 @ X0)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['110', '113'])).
% 2.04/2.25  thf('115', plain,
% 2.04/2.25      (![X0 : $i]:
% 2.04/2.25         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 2.04/2.25            = (k2_funct_1 @ X0))
% 2.04/2.25          | ~ (v2_funct_1 @ X0)
% 2.04/2.25          | ~ (v1_funct_1 @ X0)
% 2.04/2.25          | ~ (v1_relat_1 @ X0))),
% 2.04/2.25      inference('simplify', [status(thm)], ['114'])).
% 2.04/2.25  thf('116', plain,
% 2.04/2.25      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 2.04/2.25          = (k2_funct_1 @ sk_D))
% 2.04/2.25        | ~ (v1_relat_1 @ sk_D)
% 2.04/2.25        | ~ (v1_funct_1 @ sk_D)
% 2.04/2.25        | ~ (v2_funct_1 @ sk_D))),
% 2.04/2.25      inference('sup+', [status(thm)], ['109', '115'])).
% 2.04/2.25  thf('117', plain, ((v1_relat_1 @ sk_D)),
% 2.04/2.25      inference('demod', [status(thm)], ['94', '95'])).
% 2.04/2.25  thf('118', plain, ((v1_funct_1 @ sk_D)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('119', plain,
% 2.04/2.25      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 2.04/2.25          = (k2_funct_1 @ sk_D))
% 2.04/2.25        | ~ (v2_funct_1 @ sk_D))),
% 2.04/2.25      inference('demod', [status(thm)], ['116', '117', '118'])).
% 2.04/2.25  thf('120', plain, ((v2_funct_1 @ sk_D)),
% 2.04/2.25      inference('sup-', [status(thm)], ['71', '72'])).
% 2.04/2.25  thf('121', plain,
% 2.04/2.25      (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 2.04/2.25         = (k2_funct_1 @ sk_D))),
% 2.04/2.25      inference('demod', [status(thm)], ['119', '120'])).
% 2.04/2.25  thf('122', plain,
% 2.04/2.25      ((((k2_funct_1 @ sk_D) = (sk_C)) | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 2.04/2.25      inference('demod', [status(thm)], ['108', '121'])).
% 2.04/2.25  thf('123', plain,
% 2.04/2.25      ((~ (v1_relat_1 @ sk_D)
% 2.04/2.25        | ~ (v1_funct_1 @ sk_D)
% 2.04/2.25        | ((k2_funct_1 @ sk_D) = (sk_C)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['0', '122'])).
% 2.04/2.25  thf('124', plain, ((v1_relat_1 @ sk_D)),
% 2.04/2.25      inference('demod', [status(thm)], ['94', '95'])).
% 2.04/2.25  thf('125', plain, ((v1_funct_1 @ sk_D)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('126', plain, (((k2_funct_1 @ sk_D) = (sk_C))),
% 2.04/2.25      inference('demod', [status(thm)], ['123', '124', '125'])).
% 2.04/2.25  thf(t65_funct_1, axiom,
% 2.04/2.25    (![A:$i]:
% 2.04/2.25     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.04/2.25       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 2.04/2.25  thf('127', plain,
% 2.04/2.25      (![X13 : $i]:
% 2.04/2.25         (~ (v2_funct_1 @ X13)
% 2.04/2.25          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 2.04/2.25          | ~ (v1_funct_1 @ X13)
% 2.04/2.25          | ~ (v1_relat_1 @ X13))),
% 2.04/2.25      inference('cnf', [status(esa)], [t65_funct_1])).
% 2.04/2.25  thf('128', plain,
% 2.04/2.25      ((((k2_funct_1 @ sk_C) = (sk_D))
% 2.04/2.25        | ~ (v1_relat_1 @ sk_D)
% 2.04/2.25        | ~ (v1_funct_1 @ sk_D)
% 2.04/2.25        | ~ (v2_funct_1 @ sk_D))),
% 2.04/2.25      inference('sup+', [status(thm)], ['126', '127'])).
% 2.04/2.25  thf('129', plain, ((v1_relat_1 @ sk_D)),
% 2.04/2.25      inference('demod', [status(thm)], ['94', '95'])).
% 2.04/2.25  thf('130', plain, ((v1_funct_1 @ sk_D)),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('131', plain, ((v2_funct_1 @ sk_D)),
% 2.04/2.25      inference('sup-', [status(thm)], ['71', '72'])).
% 2.04/2.25  thf('132', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 2.04/2.25      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 2.04/2.25  thf('133', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('134', plain, ($false),
% 2.04/2.25      inference('simplify_reflect-', [status(thm)], ['132', '133'])).
% 2.04/2.25  
% 2.04/2.25  % SZS output end Refutation
% 2.04/2.25  
% 2.04/2.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
