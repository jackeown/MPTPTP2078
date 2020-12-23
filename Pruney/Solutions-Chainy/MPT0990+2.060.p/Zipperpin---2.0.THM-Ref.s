%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tpGWutnB3K

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:03 EST 2020

% Result     : Theorem 30.81s
% Output     : Refutation 30.81s
% Verified   : 
% Statistics : Number of formulae       :  242 ( 603 expanded)
%              Number of leaves         :   50 ( 202 expanded)
%              Depth                    :   21
%              Number of atoms          : 2444 (14016 expanded)
%              Number of equality atoms :  170 ( 982 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('1',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ X51 @ ( k2_funct_1 @ X51 ) )
        = ( k6_partfun1 @ X52 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ X51 @ ( k2_funct_1 @ X51 ) )
        = ( k6_relat_1 @ X52 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('5',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['5','8','9','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','14'])).

thf('16',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('31',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('32',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('33',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_relset_1 @ X38 @ X38 @ ( k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40 ) @ ( k6_partfun1 @ X38 ) )
      | ( ( k2_relset_1 @ X39 @ X38 @ X40 )
        = X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('37',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('38',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_relset_1 @ X38 @ X38 @ ( k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40 ) @ ( k6_relat_1 @ X38 ) )
      | ( ( k2_relset_1 @ X39 @ X38 @ X40 )
        = X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('45',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('46',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['43','47','48','49','50','51'])).

thf('53',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','52'])).

thf('54',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( zip_tseitin_0 @ X45 @ X48 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X49 @ X46 @ X46 @ X47 @ X48 @ X45 ) )
      | ( zip_tseitin_1 @ X47 @ X46 )
      | ( ( k2_relset_1 @ X49 @ X46 @ X48 )
       != X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,(
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
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('63',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('64',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['62','63','64','65','66','67'])).

thf('69',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('71',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('72',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X43 = o_0_0_xboole_0 )
      | ~ ( zip_tseitin_1 @ X43 @ X44 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf('75',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v2_funct_1 @ X42 )
      | ~ ( zip_tseitin_0 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('77',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['54','77'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('79',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('80',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('81',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('83',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('84',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('87',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['80','81','84','85','86'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('88',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('89',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
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

thf('92',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('99',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('100',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X51 ) @ X51 )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('103',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('104',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('105',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X51 ) @ X51 )
        = ( k6_relat_1 @ X50 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','105'])).

thf('107',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107','108','109','110'])).

thf('112',plain,
    ( ( sk_B = o_0_0_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('115',plain,(
    sk_B != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['112','115'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('121',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['100','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['99','126'])).

thf('128',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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

thf('129',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('130',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ X6 @ ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('137',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('141',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('142',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['139','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('148',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['134','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['133','158'])).

thf('160',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('165',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['159','160','161','162','163','164'])).

thf('166',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ X51 @ ( k2_funct_1 @ X51 ) )
        = ( k6_relat_1 @ X52 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('168',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['168','169','170','171','172'])).

thf('174',plain,
    ( ( sk_B = o_0_0_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    sk_B != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['113','114'])).

thf('176',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('178',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('180',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['178','179','180','181','182'])).

thf('184',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['165','183'])).

thf('185',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['82','83'])).

thf('186',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','184','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['82','83'])).

thf('188',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['89','186','187'])).

thf('189',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['188','189'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tpGWutnB3K
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:28:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 30.81/31.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 30.81/31.05  % Solved by: fo/fo7.sh
% 30.81/31.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 30.81/31.05  % done 4318 iterations in 30.577s
% 30.81/31.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 30.81/31.05  % SZS output start Refutation
% 30.81/31.05  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 30.81/31.05  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 30.81/31.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 30.81/31.05  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 30.81/31.05  thf(sk_A_type, type, sk_A: $i).
% 30.81/31.05  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 30.81/31.05  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 30.81/31.05  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 30.81/31.05  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 30.81/31.05  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 30.81/31.05  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 30.81/31.05  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 30.81/31.05  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 30.81/31.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 30.81/31.05  thf(sk_D_type, type, sk_D: $i).
% 30.81/31.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 30.81/31.05  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 30.81/31.05  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 30.81/31.05  thf(sk_C_type, type, sk_C: $i).
% 30.81/31.05  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 30.81/31.05  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 30.81/31.05  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 30.81/31.05  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 30.81/31.05  thf(sk_B_type, type, sk_B: $i).
% 30.81/31.05  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 30.81/31.05  thf(t36_funct_2, conjecture,
% 30.81/31.05    (![A:$i,B:$i,C:$i]:
% 30.81/31.05     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 30.81/31.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.81/31.05       ( ![D:$i]:
% 30.81/31.05         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 30.81/31.05             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 30.81/31.05           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 30.81/31.05               ( r2_relset_1 @
% 30.81/31.05                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 30.81/31.05                 ( k6_partfun1 @ A ) ) & 
% 30.81/31.05               ( v2_funct_1 @ C ) ) =>
% 30.81/31.05             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 30.81/31.05               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 30.81/31.05  thf(zf_stmt_0, negated_conjecture,
% 30.81/31.05    (~( ![A:$i,B:$i,C:$i]:
% 30.81/31.05        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 30.81/31.05            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.81/31.05          ( ![D:$i]:
% 30.81/31.05            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 30.81/31.05                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 30.81/31.05              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 30.81/31.05                  ( r2_relset_1 @
% 30.81/31.05                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 30.81/31.05                    ( k6_partfun1 @ A ) ) & 
% 30.81/31.05                  ( v2_funct_1 @ C ) ) =>
% 30.81/31.05                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 30.81/31.05                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 30.81/31.05    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 30.81/31.05  thf('0', plain,
% 30.81/31.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf(t35_funct_2, axiom,
% 30.81/31.05    (![A:$i,B:$i,C:$i]:
% 30.81/31.05     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 30.81/31.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.81/31.05       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 30.81/31.05         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 30.81/31.05           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 30.81/31.05             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 30.81/31.05  thf('1', plain,
% 30.81/31.05      (![X50 : $i, X51 : $i, X52 : $i]:
% 30.81/31.05         (((X50) = (k1_xboole_0))
% 30.81/31.05          | ~ (v1_funct_1 @ X51)
% 30.81/31.05          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 30.81/31.05          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 30.81/31.05          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_partfun1 @ X52))
% 30.81/31.05          | ~ (v2_funct_1 @ X51)
% 30.81/31.05          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 30.81/31.05      inference('cnf', [status(esa)], [t35_funct_2])).
% 30.81/31.05  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 30.81/31.05  thf('2', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 30.81/31.05      inference('cnf', [status(esa)], [d2_xboole_0])).
% 30.81/31.05  thf(redefinition_k6_partfun1, axiom,
% 30.81/31.05    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 30.81/31.05  thf('3', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 30.81/31.05      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.81/31.05  thf('4', plain,
% 30.81/31.05      (![X50 : $i, X51 : $i, X52 : $i]:
% 30.81/31.05         (((X50) = (o_0_0_xboole_0))
% 30.81/31.05          | ~ (v1_funct_1 @ X51)
% 30.81/31.05          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 30.81/31.05          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 30.81/31.05          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_relat_1 @ X52))
% 30.81/31.05          | ~ (v2_funct_1 @ X51)
% 30.81/31.05          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 30.81/31.05      inference('demod', [status(thm)], ['1', '2', '3'])).
% 30.81/31.05  thf('5', plain,
% 30.81/31.05      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 30.81/31.05        | ~ (v2_funct_1 @ sk_D)
% 30.81/31.05        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 30.81/31.05        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 30.81/31.05        | ~ (v1_funct_1 @ sk_D)
% 30.81/31.05        | ((sk_A) = (o_0_0_xboole_0)))),
% 30.81/31.05      inference('sup-', [status(thm)], ['0', '4'])).
% 30.81/31.05  thf('6', plain,
% 30.81/31.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf(redefinition_k2_relset_1, axiom,
% 30.81/31.05    (![A:$i,B:$i,C:$i]:
% 30.81/31.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.81/31.05       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 30.81/31.05  thf('7', plain,
% 30.81/31.05      (![X15 : $i, X16 : $i, X17 : $i]:
% 30.81/31.05         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 30.81/31.05          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 30.81/31.05      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 30.81/31.05  thf('8', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 30.81/31.05      inference('sup-', [status(thm)], ['6', '7'])).
% 30.81/31.05  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('11', plain,
% 30.81/31.05      ((((k2_relat_1 @ sk_D) != (sk_A))
% 30.81/31.05        | ~ (v2_funct_1 @ sk_D)
% 30.81/31.05        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 30.81/31.05        | ((sk_A) = (o_0_0_xboole_0)))),
% 30.81/31.05      inference('demod', [status(thm)], ['5', '8', '9', '10'])).
% 30.81/31.05  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('13', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 30.81/31.05      inference('cnf', [status(esa)], [d2_xboole_0])).
% 30.81/31.05  thf('14', plain, (((sk_A) != (o_0_0_xboole_0))),
% 30.81/31.05      inference('demod', [status(thm)], ['12', '13'])).
% 30.81/31.05  thf('15', plain,
% 30.81/31.05      ((((k2_relat_1 @ sk_D) != (sk_A))
% 30.81/31.05        | ~ (v2_funct_1 @ sk_D)
% 30.81/31.05        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 30.81/31.05      inference('simplify_reflect-', [status(thm)], ['11', '14'])).
% 30.81/31.05  thf('16', plain,
% 30.81/31.05      ((r2_relset_1 @ sk_A @ sk_A @ 
% 30.81/31.05        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 30.81/31.05        (k6_partfun1 @ sk_A))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('17', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 30.81/31.05      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.81/31.05  thf('18', plain,
% 30.81/31.05      ((r2_relset_1 @ sk_A @ sk_A @ 
% 30.81/31.05        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 30.81/31.05        (k6_relat_1 @ sk_A))),
% 30.81/31.05      inference('demod', [status(thm)], ['16', '17'])).
% 30.81/31.05  thf('19', plain,
% 30.81/31.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('20', plain,
% 30.81/31.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf(dt_k1_partfun1, axiom,
% 30.81/31.05    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 30.81/31.05     ( ( ( v1_funct_1 @ E ) & 
% 30.81/31.05         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 30.81/31.05         ( v1_funct_1 @ F ) & 
% 30.81/31.05         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 30.81/31.05       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 30.81/31.05         ( m1_subset_1 @
% 30.81/31.05           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 30.81/31.05           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 30.81/31.05  thf('21', plain,
% 30.81/31.05      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 30.81/31.05         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 30.81/31.05          | ~ (v1_funct_1 @ X22)
% 30.81/31.05          | ~ (v1_funct_1 @ X25)
% 30.81/31.05          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 30.81/31.05          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 30.81/31.05             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 30.81/31.05      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 30.81/31.05  thf('22', plain,
% 30.81/31.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.81/31.05         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 30.81/31.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 30.81/31.05          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 30.81/31.05          | ~ (v1_funct_1 @ X1)
% 30.81/31.05          | ~ (v1_funct_1 @ sk_C))),
% 30.81/31.05      inference('sup-', [status(thm)], ['20', '21'])).
% 30.81/31.05  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('24', plain,
% 30.81/31.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.81/31.05         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 30.81/31.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 30.81/31.05          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 30.81/31.05          | ~ (v1_funct_1 @ X1))),
% 30.81/31.05      inference('demod', [status(thm)], ['22', '23'])).
% 30.81/31.05  thf('25', plain,
% 30.81/31.05      ((~ (v1_funct_1 @ sk_D)
% 30.81/31.05        | (m1_subset_1 @ 
% 30.81/31.05           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 30.81/31.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 30.81/31.05      inference('sup-', [status(thm)], ['19', '24'])).
% 30.81/31.05  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('27', plain,
% 30.81/31.05      ((m1_subset_1 @ 
% 30.81/31.05        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 30.81/31.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.81/31.05      inference('demod', [status(thm)], ['25', '26'])).
% 30.81/31.05  thf(redefinition_r2_relset_1, axiom,
% 30.81/31.05    (![A:$i,B:$i,C:$i,D:$i]:
% 30.81/31.05     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 30.81/31.05         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.81/31.05       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 30.81/31.05  thf('28', plain,
% 30.81/31.05      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 30.81/31.05         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 30.81/31.05          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 30.81/31.05          | ((X18) = (X21))
% 30.81/31.05          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 30.81/31.05      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 30.81/31.05  thf('29', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.81/31.05             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 30.81/31.05          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 30.81/31.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 30.81/31.05      inference('sup-', [status(thm)], ['27', '28'])).
% 30.81/31.05  thf('30', plain,
% 30.81/31.05      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 30.81/31.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 30.81/31.05        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 30.81/31.05            = (k6_relat_1 @ sk_A)))),
% 30.81/31.05      inference('sup-', [status(thm)], ['18', '29'])).
% 30.81/31.05  thf(dt_k6_partfun1, axiom,
% 30.81/31.05    (![A:$i]:
% 30.81/31.05     ( ( m1_subset_1 @
% 30.81/31.05         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 30.81/31.05       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 30.81/31.05  thf('31', plain,
% 30.81/31.05      (![X29 : $i]:
% 30.81/31.05         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 30.81/31.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 30.81/31.05      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 30.81/31.05  thf('32', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 30.81/31.05      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.81/31.05  thf('33', plain,
% 30.81/31.05      (![X29 : $i]:
% 30.81/31.05         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 30.81/31.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 30.81/31.05      inference('demod', [status(thm)], ['31', '32'])).
% 30.81/31.05  thf('34', plain,
% 30.81/31.05      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 30.81/31.05         = (k6_relat_1 @ sk_A))),
% 30.81/31.05      inference('demod', [status(thm)], ['30', '33'])).
% 30.81/31.05  thf('35', plain,
% 30.81/31.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf(t24_funct_2, axiom,
% 30.81/31.05    (![A:$i,B:$i,C:$i]:
% 30.81/31.05     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 30.81/31.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.81/31.05       ( ![D:$i]:
% 30.81/31.05         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 30.81/31.05             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 30.81/31.05           ( ( r2_relset_1 @
% 30.81/31.05               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 30.81/31.05               ( k6_partfun1 @ B ) ) =>
% 30.81/31.05             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 30.81/31.05  thf('36', plain,
% 30.81/31.05      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 30.81/31.05         (~ (v1_funct_1 @ X37)
% 30.81/31.05          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 30.81/31.05          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 30.81/31.05          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 30.81/31.05               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 30.81/31.05               (k6_partfun1 @ X38))
% 30.81/31.05          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 30.81/31.05          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 30.81/31.05          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 30.81/31.05          | ~ (v1_funct_1 @ X40))),
% 30.81/31.05      inference('cnf', [status(esa)], [t24_funct_2])).
% 30.81/31.05  thf('37', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 30.81/31.05      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.81/31.05  thf('38', plain,
% 30.81/31.05      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 30.81/31.05         (~ (v1_funct_1 @ X37)
% 30.81/31.05          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 30.81/31.05          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 30.81/31.05          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 30.81/31.05               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 30.81/31.05               (k6_relat_1 @ X38))
% 30.81/31.05          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 30.81/31.05          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 30.81/31.05          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 30.81/31.05          | ~ (v1_funct_1 @ X40))),
% 30.81/31.05      inference('demod', [status(thm)], ['36', '37'])).
% 30.81/31.05  thf('39', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (~ (v1_funct_1 @ X0)
% 30.81/31.05          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 30.81/31.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 30.81/31.05          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 30.81/31.05          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.81/31.05               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 30.81/31.05               (k6_relat_1 @ sk_A))
% 30.81/31.05          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 30.81/31.05          | ~ (v1_funct_1 @ sk_C))),
% 30.81/31.05      inference('sup-', [status(thm)], ['35', '38'])).
% 30.81/31.05  thf('40', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('42', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (~ (v1_funct_1 @ X0)
% 30.81/31.05          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 30.81/31.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 30.81/31.05          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 30.81/31.05          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.81/31.05               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 30.81/31.05               (k6_relat_1 @ sk_A)))),
% 30.81/31.05      inference('demod', [status(thm)], ['39', '40', '41'])).
% 30.81/31.05  thf('43', plain,
% 30.81/31.05      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 30.81/31.05           (k6_relat_1 @ sk_A))
% 30.81/31.05        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 30.81/31.05        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 30.81/31.05        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 30.81/31.05        | ~ (v1_funct_1 @ sk_D))),
% 30.81/31.05      inference('sup-', [status(thm)], ['34', '42'])).
% 30.81/31.05  thf('44', plain,
% 30.81/31.05      (![X29 : $i]:
% 30.81/31.05         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 30.81/31.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 30.81/31.05      inference('demod', [status(thm)], ['31', '32'])).
% 30.81/31.05  thf('45', plain,
% 30.81/31.05      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 30.81/31.05         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 30.81/31.05          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 30.81/31.05          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 30.81/31.05          | ((X18) != (X21)))),
% 30.81/31.05      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 30.81/31.05  thf('46', plain,
% 30.81/31.05      (![X19 : $i, X20 : $i, X21 : $i]:
% 30.81/31.05         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 30.81/31.05          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 30.81/31.05      inference('simplify', [status(thm)], ['45'])).
% 30.81/31.05  thf('47', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 30.81/31.05      inference('sup-', [status(thm)], ['44', '46'])).
% 30.81/31.05  thf('48', plain,
% 30.81/31.05      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 30.81/31.05      inference('sup-', [status(thm)], ['6', '7'])).
% 30.81/31.05  thf('49', plain,
% 30.81/31.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('50', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('52', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 30.81/31.05      inference('demod', [status(thm)], ['43', '47', '48', '49', '50', '51'])).
% 30.81/31.05  thf('53', plain,
% 30.81/31.05      ((((sk_A) != (sk_A))
% 30.81/31.05        | ~ (v2_funct_1 @ sk_D)
% 30.81/31.05        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 30.81/31.05      inference('demod', [status(thm)], ['15', '52'])).
% 30.81/31.05  thf('54', plain,
% 30.81/31.05      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 30.81/31.05        | ~ (v2_funct_1 @ sk_D))),
% 30.81/31.05      inference('simplify', [status(thm)], ['53'])).
% 30.81/31.05  thf('55', plain,
% 30.81/31.05      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 30.81/31.05         = (k6_relat_1 @ sk_A))),
% 30.81/31.05      inference('demod', [status(thm)], ['30', '33'])).
% 30.81/31.05  thf('56', plain,
% 30.81/31.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf(t30_funct_2, axiom,
% 30.81/31.05    (![A:$i,B:$i,C:$i,D:$i]:
% 30.81/31.05     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 30.81/31.05         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 30.81/31.05       ( ![E:$i]:
% 30.81/31.05         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 30.81/31.05             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 30.81/31.05           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 30.81/31.05               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 30.81/31.05             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 30.81/31.05               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 30.81/31.05  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 30.81/31.05  thf(zf_stmt_2, axiom,
% 30.81/31.05    (![C:$i,B:$i]:
% 30.81/31.05     ( ( zip_tseitin_1 @ C @ B ) =>
% 30.81/31.05       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 30.81/31.05  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 30.81/31.05  thf(zf_stmt_4, axiom,
% 30.81/31.05    (![E:$i,D:$i]:
% 30.81/31.05     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 30.81/31.05  thf(zf_stmt_5, axiom,
% 30.81/31.05    (![A:$i,B:$i,C:$i,D:$i]:
% 30.81/31.05     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 30.81/31.05         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.81/31.05       ( ![E:$i]:
% 30.81/31.05         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 30.81/31.05             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 30.81/31.05           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 30.81/31.05               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 30.81/31.05             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 30.81/31.05  thf('57', plain,
% 30.81/31.05      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 30.81/31.05         (~ (v1_funct_1 @ X45)
% 30.81/31.05          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 30.81/31.05          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 30.81/31.05          | (zip_tseitin_0 @ X45 @ X48)
% 30.81/31.05          | ~ (v2_funct_1 @ (k1_partfun1 @ X49 @ X46 @ X46 @ X47 @ X48 @ X45))
% 30.81/31.05          | (zip_tseitin_1 @ X47 @ X46)
% 30.81/31.05          | ((k2_relset_1 @ X49 @ X46 @ X48) != (X46))
% 30.81/31.05          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X46)))
% 30.81/31.05          | ~ (v1_funct_2 @ X48 @ X49 @ X46)
% 30.81/31.05          | ~ (v1_funct_1 @ X48))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 30.81/31.05  thf('58', plain,
% 30.81/31.05      (![X0 : $i, X1 : $i]:
% 30.81/31.05         (~ (v1_funct_1 @ X0)
% 30.81/31.05          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 30.81/31.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 30.81/31.05          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 30.81/31.05          | (zip_tseitin_1 @ sk_A @ sk_B)
% 30.81/31.05          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 30.81/31.05          | (zip_tseitin_0 @ sk_D @ X0)
% 30.81/31.05          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 30.81/31.05          | ~ (v1_funct_1 @ sk_D))),
% 30.81/31.05      inference('sup-', [status(thm)], ['56', '57'])).
% 30.81/31.05  thf('59', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('61', plain,
% 30.81/31.05      (![X0 : $i, X1 : $i]:
% 30.81/31.05         (~ (v1_funct_1 @ X0)
% 30.81/31.05          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 30.81/31.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 30.81/31.05          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 30.81/31.05          | (zip_tseitin_1 @ sk_A @ sk_B)
% 30.81/31.05          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 30.81/31.05          | (zip_tseitin_0 @ sk_D @ X0))),
% 30.81/31.05      inference('demod', [status(thm)], ['58', '59', '60'])).
% 30.81/31.05  thf('62', plain,
% 30.81/31.05      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 30.81/31.05        | (zip_tseitin_0 @ sk_D @ sk_C)
% 30.81/31.05        | (zip_tseitin_1 @ sk_A @ sk_B)
% 30.81/31.05        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 30.81/31.05        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 30.81/31.05        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 30.81/31.05        | ~ (v1_funct_1 @ sk_C))),
% 30.81/31.05      inference('sup-', [status(thm)], ['55', '61'])).
% 30.81/31.05  thf(fc4_funct_1, axiom,
% 30.81/31.05    (![A:$i]:
% 30.81/31.05     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 30.81/31.05       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 30.81/31.05  thf('63', plain, (![X9 : $i]: (v2_funct_1 @ (k6_relat_1 @ X9))),
% 30.81/31.05      inference('cnf', [status(esa)], [fc4_funct_1])).
% 30.81/31.05  thf('64', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('65', plain,
% 30.81/31.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('66', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('68', plain,
% 30.81/31.05      (((zip_tseitin_0 @ sk_D @ sk_C)
% 30.81/31.05        | (zip_tseitin_1 @ sk_A @ sk_B)
% 30.81/31.05        | ((sk_B) != (sk_B)))),
% 30.81/31.05      inference('demod', [status(thm)], ['62', '63', '64', '65', '66', '67'])).
% 30.81/31.05  thf('69', plain,
% 30.81/31.05      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 30.81/31.05      inference('simplify', [status(thm)], ['68'])).
% 30.81/31.05  thf('70', plain,
% 30.81/31.05      (![X43 : $i, X44 : $i]:
% 30.81/31.05         (((X43) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X43 @ X44))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_2])).
% 30.81/31.05  thf('71', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 30.81/31.05      inference('cnf', [status(esa)], [d2_xboole_0])).
% 30.81/31.05  thf('72', plain,
% 30.81/31.05      (![X43 : $i, X44 : $i]:
% 30.81/31.05         (((X43) = (o_0_0_xboole_0)) | ~ (zip_tseitin_1 @ X43 @ X44))),
% 30.81/31.05      inference('demod', [status(thm)], ['70', '71'])).
% 30.81/31.05  thf('73', plain,
% 30.81/31.05      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (o_0_0_xboole_0)))),
% 30.81/31.05      inference('sup-', [status(thm)], ['69', '72'])).
% 30.81/31.05  thf('74', plain, (((sk_A) != (o_0_0_xboole_0))),
% 30.81/31.05      inference('demod', [status(thm)], ['12', '13'])).
% 30.81/31.05  thf('75', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 30.81/31.05      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 30.81/31.05  thf('76', plain,
% 30.81/31.05      (![X41 : $i, X42 : $i]:
% 30.81/31.05         ((v2_funct_1 @ X42) | ~ (zip_tseitin_0 @ X42 @ X41))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_4])).
% 30.81/31.05  thf('77', plain, ((v2_funct_1 @ sk_D)),
% 30.81/31.05      inference('sup-', [status(thm)], ['75', '76'])).
% 30.81/31.05  thf('78', plain,
% 30.81/31.05      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 30.81/31.05      inference('demod', [status(thm)], ['54', '77'])).
% 30.81/31.05  thf(t58_funct_1, axiom,
% 30.81/31.05    (![A:$i]:
% 30.81/31.05     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 30.81/31.05       ( ( v2_funct_1 @ A ) =>
% 30.81/31.05         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 30.81/31.05             ( k1_relat_1 @ A ) ) & 
% 30.81/31.05           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 30.81/31.05             ( k1_relat_1 @ A ) ) ) ) ))).
% 30.81/31.05  thf('79', plain,
% 30.81/31.05      (![X11 : $i]:
% 30.81/31.05         (~ (v2_funct_1 @ X11)
% 30.81/31.05          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ (k2_funct_1 @ X11)))
% 30.81/31.05              = (k1_relat_1 @ X11))
% 30.81/31.05          | ~ (v1_funct_1 @ X11)
% 30.81/31.05          | ~ (v1_relat_1 @ X11))),
% 30.81/31.05      inference('cnf', [status(esa)], [t58_funct_1])).
% 30.81/31.05  thf('80', plain,
% 30.81/31.05      ((((k2_relat_1 @ (k6_relat_1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 30.81/31.05        | ~ (v1_relat_1 @ sk_D)
% 30.81/31.05        | ~ (v1_funct_1 @ sk_D)
% 30.81/31.05        | ~ (v2_funct_1 @ sk_D))),
% 30.81/31.05      inference('sup+', [status(thm)], ['78', '79'])).
% 30.81/31.05  thf(t71_relat_1, axiom,
% 30.81/31.05    (![A:$i]:
% 30.81/31.05     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 30.81/31.05       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 30.81/31.05  thf('81', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 30.81/31.05      inference('cnf', [status(esa)], [t71_relat_1])).
% 30.81/31.05  thf('82', plain,
% 30.81/31.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf(cc1_relset_1, axiom,
% 30.81/31.05    (![A:$i,B:$i,C:$i]:
% 30.81/31.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.81/31.05       ( v1_relat_1 @ C ) ))).
% 30.81/31.05  thf('83', plain,
% 30.81/31.05      (![X12 : $i, X13 : $i, X14 : $i]:
% 30.81/31.05         ((v1_relat_1 @ X12)
% 30.81/31.05          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 30.81/31.05      inference('cnf', [status(esa)], [cc1_relset_1])).
% 30.81/31.05  thf('84', plain, ((v1_relat_1 @ sk_D)),
% 30.81/31.05      inference('sup-', [status(thm)], ['82', '83'])).
% 30.81/31.05  thf('85', plain, ((v1_funct_1 @ sk_D)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('86', plain, ((v2_funct_1 @ sk_D)),
% 30.81/31.05      inference('sup-', [status(thm)], ['75', '76'])).
% 30.81/31.05  thf('87', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 30.81/31.05      inference('demod', [status(thm)], ['80', '81', '84', '85', '86'])).
% 30.81/31.05  thf(t78_relat_1, axiom,
% 30.81/31.05    (![A:$i]:
% 30.81/31.05     ( ( v1_relat_1 @ A ) =>
% 30.81/31.05       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 30.81/31.05  thf('88', plain,
% 30.81/31.05      (![X5 : $i]:
% 30.81/31.05         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 30.81/31.05          | ~ (v1_relat_1 @ X5))),
% 30.81/31.05      inference('cnf', [status(esa)], [t78_relat_1])).
% 30.81/31.05  thf('89', plain,
% 30.81/31.05      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (sk_D))
% 30.81/31.05        | ~ (v1_relat_1 @ sk_D))),
% 30.81/31.05      inference('sup+', [status(thm)], ['87', '88'])).
% 30.81/31.05  thf('90', plain,
% 30.81/31.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('91', plain,
% 30.81/31.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf(redefinition_k1_partfun1, axiom,
% 30.81/31.05    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 30.81/31.05     ( ( ( v1_funct_1 @ E ) & 
% 30.81/31.05         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 30.81/31.05         ( v1_funct_1 @ F ) & 
% 30.81/31.05         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 30.81/31.05       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 30.81/31.05  thf('92', plain,
% 30.81/31.05      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 30.81/31.05         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 30.81/31.05          | ~ (v1_funct_1 @ X30)
% 30.81/31.05          | ~ (v1_funct_1 @ X33)
% 30.81/31.05          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 30.81/31.05          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 30.81/31.05              = (k5_relat_1 @ X30 @ X33)))),
% 30.81/31.05      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 30.81/31.05  thf('93', plain,
% 30.81/31.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.81/31.05         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 30.81/31.05            = (k5_relat_1 @ sk_C @ X0))
% 30.81/31.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 30.81/31.05          | ~ (v1_funct_1 @ X0)
% 30.81/31.05          | ~ (v1_funct_1 @ sk_C))),
% 30.81/31.05      inference('sup-', [status(thm)], ['91', '92'])).
% 30.81/31.05  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('95', plain,
% 30.81/31.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.81/31.05         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 30.81/31.05            = (k5_relat_1 @ sk_C @ X0))
% 30.81/31.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 30.81/31.05          | ~ (v1_funct_1 @ X0))),
% 30.81/31.05      inference('demod', [status(thm)], ['93', '94'])).
% 30.81/31.05  thf('96', plain,
% 30.81/31.05      ((~ (v1_funct_1 @ sk_D)
% 30.81/31.05        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 30.81/31.05            = (k5_relat_1 @ sk_C @ sk_D)))),
% 30.81/31.05      inference('sup-', [status(thm)], ['90', '95'])).
% 30.81/31.05  thf('97', plain, ((v1_funct_1 @ sk_D)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('98', plain,
% 30.81/31.05      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 30.81/31.05         = (k6_relat_1 @ sk_A))),
% 30.81/31.05      inference('demod', [status(thm)], ['30', '33'])).
% 30.81/31.05  thf('99', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 30.81/31.05      inference('demod', [status(thm)], ['96', '97', '98'])).
% 30.81/31.05  thf(dt_k2_funct_1, axiom,
% 30.81/31.05    (![A:$i]:
% 30.81/31.05     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 30.81/31.05       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 30.81/31.05         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 30.81/31.05  thf('100', plain,
% 30.81/31.05      (![X7 : $i]:
% 30.81/31.05         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 30.81/31.05          | ~ (v1_funct_1 @ X7)
% 30.81/31.05          | ~ (v1_relat_1 @ X7))),
% 30.81/31.05      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.81/31.05  thf('101', plain,
% 30.81/31.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('102', plain,
% 30.81/31.05      (![X50 : $i, X51 : $i, X52 : $i]:
% 30.81/31.05         (((X50) = (k1_xboole_0))
% 30.81/31.05          | ~ (v1_funct_1 @ X51)
% 30.81/31.05          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 30.81/31.05          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 30.81/31.05          | ((k5_relat_1 @ (k2_funct_1 @ X51) @ X51) = (k6_partfun1 @ X50))
% 30.81/31.05          | ~ (v2_funct_1 @ X51)
% 30.81/31.05          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 30.81/31.05      inference('cnf', [status(esa)], [t35_funct_2])).
% 30.81/31.05  thf('103', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 30.81/31.05      inference('cnf', [status(esa)], [d2_xboole_0])).
% 30.81/31.05  thf('104', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 30.81/31.05      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.81/31.05  thf('105', plain,
% 30.81/31.05      (![X50 : $i, X51 : $i, X52 : $i]:
% 30.81/31.05         (((X50) = (o_0_0_xboole_0))
% 30.81/31.05          | ~ (v1_funct_1 @ X51)
% 30.81/31.05          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 30.81/31.05          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 30.81/31.05          | ((k5_relat_1 @ (k2_funct_1 @ X51) @ X51) = (k6_relat_1 @ X50))
% 30.81/31.05          | ~ (v2_funct_1 @ X51)
% 30.81/31.05          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 30.81/31.05      inference('demod', [status(thm)], ['102', '103', '104'])).
% 30.81/31.05  thf('106', plain,
% 30.81/31.05      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 30.81/31.05        | ~ (v2_funct_1 @ sk_C)
% 30.81/31.05        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 30.81/31.05        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 30.81/31.05        | ~ (v1_funct_1 @ sk_C)
% 30.81/31.05        | ((sk_B) = (o_0_0_xboole_0)))),
% 30.81/31.05      inference('sup-', [status(thm)], ['101', '105'])).
% 30.81/31.05  thf('107', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('109', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('111', plain,
% 30.81/31.05      ((((sk_B) != (sk_B))
% 30.81/31.05        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 30.81/31.05        | ((sk_B) = (o_0_0_xboole_0)))),
% 30.81/31.05      inference('demod', [status(thm)], ['106', '107', '108', '109', '110'])).
% 30.81/31.05  thf('112', plain,
% 30.81/31.05      ((((sk_B) = (o_0_0_xboole_0))
% 30.81/31.05        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 30.81/31.05      inference('simplify', [status(thm)], ['111'])).
% 30.81/31.05  thf('113', plain, (((sk_B) != (k1_xboole_0))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('114', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 30.81/31.05      inference('cnf', [status(esa)], [d2_xboole_0])).
% 30.81/31.05  thf('115', plain, (((sk_B) != (o_0_0_xboole_0))),
% 30.81/31.05      inference('demod', [status(thm)], ['113', '114'])).
% 30.81/31.05  thf('116', plain,
% 30.81/31.05      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 30.81/31.05      inference('simplify_reflect-', [status(thm)], ['112', '115'])).
% 30.81/31.05  thf(t55_relat_1, axiom,
% 30.81/31.05    (![A:$i]:
% 30.81/31.05     ( ( v1_relat_1 @ A ) =>
% 30.81/31.05       ( ![B:$i]:
% 30.81/31.05         ( ( v1_relat_1 @ B ) =>
% 30.81/31.05           ( ![C:$i]:
% 30.81/31.05             ( ( v1_relat_1 @ C ) =>
% 30.81/31.05               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 30.81/31.05                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 30.81/31.05  thf('117', plain,
% 30.81/31.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.81/31.05         (~ (v1_relat_1 @ X0)
% 30.81/31.05          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 30.81/31.05              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 30.81/31.05          | ~ (v1_relat_1 @ X2)
% 30.81/31.05          | ~ (v1_relat_1 @ X1))),
% 30.81/31.05      inference('cnf', [status(esa)], [t55_relat_1])).
% 30.81/31.05  thf('118', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 30.81/31.05            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 30.81/31.05          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 30.81/31.05          | ~ (v1_relat_1 @ X0)
% 30.81/31.05          | ~ (v1_relat_1 @ sk_C))),
% 30.81/31.05      inference('sup+', [status(thm)], ['116', '117'])).
% 30.81/31.05  thf('119', plain,
% 30.81/31.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('120', plain,
% 30.81/31.05      (![X12 : $i, X13 : $i, X14 : $i]:
% 30.81/31.05         ((v1_relat_1 @ X12)
% 30.81/31.05          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 30.81/31.05      inference('cnf', [status(esa)], [cc1_relset_1])).
% 30.81/31.05  thf('121', plain, ((v1_relat_1 @ sk_C)),
% 30.81/31.05      inference('sup-', [status(thm)], ['119', '120'])).
% 30.81/31.05  thf('122', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 30.81/31.05            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 30.81/31.05          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 30.81/31.05          | ~ (v1_relat_1 @ X0))),
% 30.81/31.05      inference('demod', [status(thm)], ['118', '121'])).
% 30.81/31.05  thf('123', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (~ (v1_relat_1 @ sk_C)
% 30.81/31.05          | ~ (v1_funct_1 @ sk_C)
% 30.81/31.05          | ~ (v1_relat_1 @ X0)
% 30.81/31.05          | ((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 30.81/31.05              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 30.81/31.05      inference('sup-', [status(thm)], ['100', '122'])).
% 30.81/31.05  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 30.81/31.05      inference('sup-', [status(thm)], ['119', '120'])).
% 30.81/31.05  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('126', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (~ (v1_relat_1 @ X0)
% 30.81/31.05          | ((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 30.81/31.05              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 30.81/31.05      inference('demod', [status(thm)], ['123', '124', '125'])).
% 30.81/31.05  thf('127', plain,
% 30.81/31.05      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D)
% 30.81/31.05          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 30.81/31.05        | ~ (v1_relat_1 @ sk_D))),
% 30.81/31.05      inference('sup+', [status(thm)], ['99', '126'])).
% 30.81/31.05  thf('128', plain,
% 30.81/31.05      (![X7 : $i]:
% 30.81/31.05         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 30.81/31.05          | ~ (v1_funct_1 @ X7)
% 30.81/31.05          | ~ (v1_relat_1 @ X7))),
% 30.81/31.05      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.81/31.05  thf(t55_funct_1, axiom,
% 30.81/31.05    (![A:$i]:
% 30.81/31.05     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 30.81/31.05       ( ( v2_funct_1 @ A ) =>
% 30.81/31.05         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 30.81/31.05           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 30.81/31.05  thf('129', plain,
% 30.81/31.05      (![X10 : $i]:
% 30.81/31.05         (~ (v2_funct_1 @ X10)
% 30.81/31.05          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 30.81/31.05          | ~ (v1_funct_1 @ X10)
% 30.81/31.05          | ~ (v1_relat_1 @ X10))),
% 30.81/31.05      inference('cnf', [status(esa)], [t55_funct_1])).
% 30.81/31.05  thf(t80_relat_1, axiom,
% 30.81/31.05    (![A:$i]:
% 30.81/31.05     ( ( v1_relat_1 @ A ) =>
% 30.81/31.05       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 30.81/31.05  thf('130', plain,
% 30.81/31.05      (![X6 : $i]:
% 30.81/31.05         (((k5_relat_1 @ X6 @ (k6_relat_1 @ (k2_relat_1 @ X6))) = (X6))
% 30.81/31.05          | ~ (v1_relat_1 @ X6))),
% 30.81/31.05      inference('cnf', [status(esa)], [t80_relat_1])).
% 30.81/31.05  thf('131', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 30.81/31.05            = (k2_funct_1 @ X0))
% 30.81/31.05          | ~ (v1_relat_1 @ X0)
% 30.81/31.05          | ~ (v1_funct_1 @ X0)
% 30.81/31.05          | ~ (v2_funct_1 @ X0)
% 30.81/31.05          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 30.81/31.05      inference('sup+', [status(thm)], ['129', '130'])).
% 30.81/31.05  thf('132', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (~ (v1_relat_1 @ X0)
% 30.81/31.05          | ~ (v1_funct_1 @ X0)
% 30.81/31.05          | ~ (v2_funct_1 @ X0)
% 30.81/31.05          | ~ (v1_funct_1 @ X0)
% 30.81/31.05          | ~ (v1_relat_1 @ X0)
% 30.81/31.05          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 30.81/31.05              = (k2_funct_1 @ X0)))),
% 30.81/31.05      inference('sup-', [status(thm)], ['128', '131'])).
% 30.81/31.05  thf('133', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 30.81/31.05            = (k2_funct_1 @ X0))
% 30.81/31.05          | ~ (v2_funct_1 @ X0)
% 30.81/31.05          | ~ (v1_funct_1 @ X0)
% 30.81/31.05          | ~ (v1_relat_1 @ X0))),
% 30.81/31.05      inference('simplify', [status(thm)], ['132'])).
% 30.81/31.05  thf('134', plain,
% 30.81/31.05      (![X7 : $i]:
% 30.81/31.05         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 30.81/31.05          | ~ (v1_funct_1 @ X7)
% 30.81/31.05          | ~ (v1_relat_1 @ X7))),
% 30.81/31.05      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.81/31.05  thf('135', plain,
% 30.81/31.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('136', plain,
% 30.81/31.05      (![X15 : $i, X16 : $i, X17 : $i]:
% 30.81/31.05         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 30.81/31.05          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 30.81/31.05      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 30.81/31.05  thf('137', plain,
% 30.81/31.05      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 30.81/31.05      inference('sup-', [status(thm)], ['135', '136'])).
% 30.81/31.05  thf('138', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('139', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 30.81/31.05      inference('sup+', [status(thm)], ['137', '138'])).
% 30.81/31.05  thf('140', plain,
% 30.81/31.05      (![X7 : $i]:
% 30.81/31.05         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 30.81/31.05          | ~ (v1_funct_1 @ X7)
% 30.81/31.05          | ~ (v1_relat_1 @ X7))),
% 30.81/31.05      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.81/31.05  thf('141', plain,
% 30.81/31.05      (![X10 : $i]:
% 30.81/31.05         (~ (v2_funct_1 @ X10)
% 30.81/31.05          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 30.81/31.05          | ~ (v1_funct_1 @ X10)
% 30.81/31.05          | ~ (v1_relat_1 @ X10))),
% 30.81/31.05      inference('cnf', [status(esa)], [t55_funct_1])).
% 30.81/31.05  thf('142', plain,
% 30.81/31.05      (![X5 : $i]:
% 30.81/31.05         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 30.81/31.05          | ~ (v1_relat_1 @ X5))),
% 30.81/31.05      inference('cnf', [status(esa)], [t78_relat_1])).
% 30.81/31.05  thf('143', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 30.81/31.05            = (k2_funct_1 @ X0))
% 30.81/31.05          | ~ (v1_relat_1 @ X0)
% 30.81/31.05          | ~ (v1_funct_1 @ X0)
% 30.81/31.05          | ~ (v2_funct_1 @ X0)
% 30.81/31.05          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 30.81/31.05      inference('sup+', [status(thm)], ['141', '142'])).
% 30.81/31.05  thf('144', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (~ (v1_relat_1 @ X0)
% 30.81/31.05          | ~ (v1_funct_1 @ X0)
% 30.81/31.05          | ~ (v2_funct_1 @ X0)
% 30.81/31.05          | ~ (v1_funct_1 @ X0)
% 30.81/31.05          | ~ (v1_relat_1 @ X0)
% 30.81/31.05          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 30.81/31.05              = (k2_funct_1 @ X0)))),
% 30.81/31.05      inference('sup-', [status(thm)], ['140', '143'])).
% 30.81/31.05  thf('145', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 30.81/31.05            = (k2_funct_1 @ X0))
% 30.81/31.05          | ~ (v2_funct_1 @ X0)
% 30.81/31.05          | ~ (v1_funct_1 @ X0)
% 30.81/31.05          | ~ (v1_relat_1 @ X0))),
% 30.81/31.05      inference('simplify', [status(thm)], ['144'])).
% 30.81/31.05  thf('146', plain,
% 30.81/31.05      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 30.81/31.05          = (k2_funct_1 @ sk_C))
% 30.81/31.05        | ~ (v1_relat_1 @ sk_C)
% 30.81/31.05        | ~ (v1_funct_1 @ sk_C)
% 30.81/31.05        | ~ (v2_funct_1 @ sk_C))),
% 30.81/31.05      inference('sup+', [status(thm)], ['139', '145'])).
% 30.81/31.05  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 30.81/31.05      inference('sup-', [status(thm)], ['119', '120'])).
% 30.81/31.05  thf('148', plain, ((v1_funct_1 @ sk_C)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('149', plain, ((v2_funct_1 @ sk_C)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('150', plain,
% 30.81/31.05      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 30.81/31.05         = (k2_funct_1 @ sk_C))),
% 30.81/31.05      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 30.81/31.05  thf('151', plain,
% 30.81/31.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.81/31.05         (~ (v1_relat_1 @ X0)
% 30.81/31.05          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 30.81/31.05              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 30.81/31.05          | ~ (v1_relat_1 @ X2)
% 30.81/31.05          | ~ (v1_relat_1 @ X1))),
% 30.81/31.05      inference('cnf', [status(esa)], [t55_relat_1])).
% 30.81/31.05  thf('152', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 30.81/31.05            = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 30.81/31.05               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 30.81/31.05          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 30.81/31.05          | ~ (v1_relat_1 @ X0)
% 30.81/31.05          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 30.81/31.05      inference('sup+', [status(thm)], ['150', '151'])).
% 30.81/31.05  thf('153', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 30.81/31.05      inference('cnf', [status(esa)], [fc4_funct_1])).
% 30.81/31.05  thf('154', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 30.81/31.05            = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 30.81/31.05               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 30.81/31.05          | ~ (v1_relat_1 @ X0)
% 30.81/31.05          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 30.81/31.05      inference('demod', [status(thm)], ['152', '153'])).
% 30.81/31.05  thf('155', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (~ (v1_relat_1 @ sk_C)
% 30.81/31.05          | ~ (v1_funct_1 @ sk_C)
% 30.81/31.05          | ~ (v1_relat_1 @ X0)
% 30.81/31.05          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 30.81/31.05              = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 30.81/31.05                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 30.81/31.05      inference('sup-', [status(thm)], ['134', '154'])).
% 30.81/31.05  thf('156', plain, ((v1_relat_1 @ sk_C)),
% 30.81/31.05      inference('sup-', [status(thm)], ['119', '120'])).
% 30.81/31.05  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('158', plain,
% 30.81/31.05      (![X0 : $i]:
% 30.81/31.05         (~ (v1_relat_1 @ X0)
% 30.81/31.05          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 30.81/31.05              = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 30.81/31.05                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 30.81/31.05      inference('demod', [status(thm)], ['155', '156', '157'])).
% 30.81/31.05  thf('159', plain,
% 30.81/31.05      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 30.81/31.05          = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 30.81/31.05        | ~ (v1_relat_1 @ sk_C)
% 30.81/31.05        | ~ (v1_funct_1 @ sk_C)
% 30.81/31.05        | ~ (v2_funct_1 @ sk_C)
% 30.81/31.05        | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_C))))),
% 30.81/31.05      inference('sup+', [status(thm)], ['133', '158'])).
% 30.81/31.05  thf('160', plain,
% 30.81/31.05      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 30.81/31.05         = (k2_funct_1 @ sk_C))),
% 30.81/31.05      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 30.81/31.05  thf('161', plain, ((v1_relat_1 @ sk_C)),
% 30.81/31.05      inference('sup-', [status(thm)], ['119', '120'])).
% 30.81/31.05  thf('162', plain, ((v1_funct_1 @ sk_C)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('163', plain, ((v2_funct_1 @ sk_C)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('164', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 30.81/31.05      inference('cnf', [status(esa)], [fc4_funct_1])).
% 30.81/31.05  thf('165', plain,
% 30.81/31.05      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 30.81/31.05         = (k2_funct_1 @ sk_C))),
% 30.81/31.05      inference('demod', [status(thm)],
% 30.81/31.05                ['159', '160', '161', '162', '163', '164'])).
% 30.81/31.05  thf('166', plain,
% 30.81/31.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('167', plain,
% 30.81/31.05      (![X50 : $i, X51 : $i, X52 : $i]:
% 30.81/31.05         (((X50) = (o_0_0_xboole_0))
% 30.81/31.05          | ~ (v1_funct_1 @ X51)
% 30.81/31.05          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 30.81/31.05          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 30.81/31.05          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_relat_1 @ X52))
% 30.81/31.05          | ~ (v2_funct_1 @ X51)
% 30.81/31.05          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 30.81/31.05      inference('demod', [status(thm)], ['1', '2', '3'])).
% 30.81/31.05  thf('168', plain,
% 30.81/31.05      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 30.81/31.05        | ~ (v2_funct_1 @ sk_C)
% 30.81/31.05        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 30.81/31.05        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 30.81/31.05        | ~ (v1_funct_1 @ sk_C)
% 30.81/31.05        | ((sk_B) = (o_0_0_xboole_0)))),
% 30.81/31.05      inference('sup-', [status(thm)], ['166', '167'])).
% 30.81/31.05  thf('169', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('170', plain, ((v2_funct_1 @ sk_C)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('171', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('172', plain, ((v1_funct_1 @ sk_C)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('173', plain,
% 30.81/31.05      ((((sk_B) != (sk_B))
% 30.81/31.05        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 30.81/31.05        | ((sk_B) = (o_0_0_xboole_0)))),
% 30.81/31.05      inference('demod', [status(thm)], ['168', '169', '170', '171', '172'])).
% 30.81/31.05  thf('174', plain,
% 30.81/31.05      ((((sk_B) = (o_0_0_xboole_0))
% 30.81/31.05        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 30.81/31.05      inference('simplify', [status(thm)], ['173'])).
% 30.81/31.05  thf('175', plain, (((sk_B) != (o_0_0_xboole_0))),
% 30.81/31.05      inference('demod', [status(thm)], ['113', '114'])).
% 30.81/31.05  thf('176', plain,
% 30.81/31.05      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 30.81/31.05      inference('simplify_reflect-', [status(thm)], ['174', '175'])).
% 30.81/31.05  thf('177', plain,
% 30.81/31.05      (![X11 : $i]:
% 30.81/31.05         (~ (v2_funct_1 @ X11)
% 30.81/31.05          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ (k2_funct_1 @ X11)))
% 30.81/31.05              = (k1_relat_1 @ X11))
% 30.81/31.05          | ~ (v1_funct_1 @ X11)
% 30.81/31.05          | ~ (v1_relat_1 @ X11))),
% 30.81/31.05      inference('cnf', [status(esa)], [t58_funct_1])).
% 30.81/31.05  thf('178', plain,
% 30.81/31.05      ((((k2_relat_1 @ (k6_relat_1 @ sk_A)) = (k1_relat_1 @ sk_C))
% 30.81/31.05        | ~ (v1_relat_1 @ sk_C)
% 30.81/31.05        | ~ (v1_funct_1 @ sk_C)
% 30.81/31.05        | ~ (v2_funct_1 @ sk_C))),
% 30.81/31.05      inference('sup+', [status(thm)], ['176', '177'])).
% 30.81/31.05  thf('179', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 30.81/31.05      inference('cnf', [status(esa)], [t71_relat_1])).
% 30.81/31.05  thf('180', plain, ((v1_relat_1 @ sk_C)),
% 30.81/31.05      inference('sup-', [status(thm)], ['119', '120'])).
% 30.81/31.05  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('182', plain, ((v2_funct_1 @ sk_C)),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('183', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 30.81/31.05      inference('demod', [status(thm)], ['178', '179', '180', '181', '182'])).
% 30.81/31.05  thf('184', plain,
% 30.81/31.05      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A))
% 30.81/31.05         = (k2_funct_1 @ sk_C))),
% 30.81/31.05      inference('demod', [status(thm)], ['165', '183'])).
% 30.81/31.05  thf('185', plain, ((v1_relat_1 @ sk_D)),
% 30.81/31.05      inference('sup-', [status(thm)], ['82', '83'])).
% 30.81/31.05  thf('186', plain,
% 30.81/31.05      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 30.81/31.05      inference('demod', [status(thm)], ['127', '184', '185'])).
% 30.81/31.05  thf('187', plain, ((v1_relat_1 @ sk_D)),
% 30.81/31.05      inference('sup-', [status(thm)], ['82', '83'])).
% 30.81/31.05  thf('188', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 30.81/31.05      inference('demod', [status(thm)], ['89', '186', '187'])).
% 30.81/31.05  thf('189', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 30.81/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.81/31.05  thf('190', plain, ($false),
% 30.81/31.05      inference('simplify_reflect-', [status(thm)], ['188', '189'])).
% 30.81/31.05  
% 30.81/31.05  % SZS output end Refutation
% 30.81/31.05  
% 30.81/31.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
