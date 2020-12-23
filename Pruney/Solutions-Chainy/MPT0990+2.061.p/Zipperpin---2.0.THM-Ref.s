%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mUq7fvwXpI

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:04 EST 2020

% Result     : Theorem 32.10s
% Output     : Refutation 32.10s
% Verified   : 
% Statistics : Number of formulae       :  244 ( 615 expanded)
%              Number of leaves         :   50 ( 206 expanded)
%              Depth                    :   21
%              Number of atoms          : 2456 (14100 expanded)
%              Number of equality atoms :  170 ( 986 expanded)
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

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ X50 @ ( k2_funct_1 @ X50 ) )
        = ( k6_relat_1 @ X51 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
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
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X26 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
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
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('32',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('33',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
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

thf('37',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('38',plain,(
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
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('45',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('46',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('63',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

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
    ! [X42: $i,X43: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('71',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('72',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X42 = o_0_0_xboole_0 )
      | ~ ( zip_tseitin_1 @ X42 @ X43 ) ) ),
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
    ! [X40: $i,X41: $i] :
      ( ( v2_funct_1 @ X41 )
      | ~ ( zip_tseitin_0 @ X41 @ X40 ) ) ),
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
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) ) )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
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
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X50 ) @ X50 )
        = ( k6_partfun1 @ X49 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('103',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('104',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('105',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X50 ) @ X50 )
        = ( k6_relat_1 @ X49 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('154',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('155',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['152','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['134','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['133','160'])).

thf('162',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('163',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('164',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('167',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['161','162','163','164','165','166'])).

thf('168',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ X50 @ ( k2_funct_1 @ X50 ) )
        = ( k6_relat_1 @ X51 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('170',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['170','171','172','173','174'])).

thf('176',plain,
    ( ( sk_B = o_0_0_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    sk_B != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['113','114'])).

thf('178',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) ) )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('180',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('182',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['180','181','182','183','184'])).

thf('186',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['167','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['82','83'])).

thf('188',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','186','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['82','83'])).

thf('190',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['89','188','189'])).

thf('191',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['190','191'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mUq7fvwXpI
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:41:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 32.10/32.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 32.10/32.32  % Solved by: fo/fo7.sh
% 32.10/32.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 32.10/32.32  % done 4318 iterations in 31.855s
% 32.10/32.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 32.10/32.32  % SZS output start Refutation
% 32.10/32.32  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 32.10/32.32  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 32.10/32.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 32.10/32.32  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 32.10/32.32  thf(sk_B_type, type, sk_B: $i).
% 32.10/32.32  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 32.10/32.32  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 32.10/32.32  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 32.10/32.32  thf(sk_A_type, type, sk_A: $i).
% 32.10/32.32  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 32.10/32.32  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 32.10/32.32  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 32.10/32.32  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 32.10/32.32  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 32.10/32.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 32.10/32.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 32.10/32.32  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 32.10/32.32  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 32.10/32.32  thf(sk_D_type, type, sk_D: $i).
% 32.10/32.32  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 32.10/32.32  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 32.10/32.32  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 32.10/32.32  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 32.10/32.32  thf(sk_C_type, type, sk_C: $i).
% 32.10/32.32  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 32.10/32.32  thf(t36_funct_2, conjecture,
% 32.10/32.32    (![A:$i,B:$i,C:$i]:
% 32.10/32.32     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 32.10/32.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.10/32.32       ( ![D:$i]:
% 32.10/32.32         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 32.10/32.32             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 32.10/32.32           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 32.10/32.32               ( r2_relset_1 @
% 32.10/32.32                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 32.10/32.32                 ( k6_partfun1 @ A ) ) & 
% 32.10/32.32               ( v2_funct_1 @ C ) ) =>
% 32.10/32.32             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 32.10/32.32               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 32.10/32.32  thf(zf_stmt_0, negated_conjecture,
% 32.10/32.32    (~( ![A:$i,B:$i,C:$i]:
% 32.10/32.32        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 32.10/32.32            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.10/32.32          ( ![D:$i]:
% 32.10/32.32            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 32.10/32.32                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 32.10/32.32              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 32.10/32.32                  ( r2_relset_1 @
% 32.10/32.32                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 32.10/32.32                    ( k6_partfun1 @ A ) ) & 
% 32.10/32.32                  ( v2_funct_1 @ C ) ) =>
% 32.10/32.32                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 32.10/32.32                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 32.10/32.32    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 32.10/32.32  thf('0', plain,
% 32.10/32.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf(t35_funct_2, axiom,
% 32.10/32.32    (![A:$i,B:$i,C:$i]:
% 32.10/32.32     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 32.10/32.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.10/32.32       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 32.10/32.32         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 32.10/32.32           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 32.10/32.32             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 32.10/32.32  thf('1', plain,
% 32.10/32.32      (![X49 : $i, X50 : $i, X51 : $i]:
% 32.10/32.32         (((X49) = (k1_xboole_0))
% 32.10/32.32          | ~ (v1_funct_1 @ X50)
% 32.10/32.32          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 32.10/32.32          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 32.10/32.32          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_partfun1 @ X51))
% 32.10/32.32          | ~ (v2_funct_1 @ X50)
% 32.10/32.32          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 32.10/32.32      inference('cnf', [status(esa)], [t35_funct_2])).
% 32.10/32.32  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 32.10/32.32  thf('2', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 32.10/32.32      inference('cnf', [status(esa)], [d2_xboole_0])).
% 32.10/32.32  thf(redefinition_k6_partfun1, axiom,
% 32.10/32.32    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 32.10/32.32  thf('3', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 32.10/32.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 32.10/32.32  thf('4', plain,
% 32.10/32.32      (![X49 : $i, X50 : $i, X51 : $i]:
% 32.10/32.32         (((X49) = (o_0_0_xboole_0))
% 32.10/32.32          | ~ (v1_funct_1 @ X50)
% 32.10/32.32          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 32.10/32.32          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 32.10/32.32          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_relat_1 @ X51))
% 32.10/32.32          | ~ (v2_funct_1 @ X50)
% 32.10/32.32          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 32.10/32.32      inference('demod', [status(thm)], ['1', '2', '3'])).
% 32.10/32.32  thf('5', plain,
% 32.10/32.32      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 32.10/32.32        | ~ (v2_funct_1 @ sk_D)
% 32.10/32.32        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 32.10/32.32        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 32.10/32.32        | ~ (v1_funct_1 @ sk_D)
% 32.10/32.32        | ((sk_A) = (o_0_0_xboole_0)))),
% 32.10/32.32      inference('sup-', [status(thm)], ['0', '4'])).
% 32.10/32.32  thf('6', plain,
% 32.10/32.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf(redefinition_k2_relset_1, axiom,
% 32.10/32.32    (![A:$i,B:$i,C:$i]:
% 32.10/32.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.10/32.32       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 32.10/32.32  thf('7', plain,
% 32.10/32.32      (![X14 : $i, X15 : $i, X16 : $i]:
% 32.10/32.32         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 32.10/32.32          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 32.10/32.32      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 32.10/32.32  thf('8', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 32.10/32.32      inference('sup-', [status(thm)], ['6', '7'])).
% 32.10/32.32  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('11', plain,
% 32.10/32.32      ((((k2_relat_1 @ sk_D) != (sk_A))
% 32.10/32.32        | ~ (v2_funct_1 @ sk_D)
% 32.10/32.32        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 32.10/32.32        | ((sk_A) = (o_0_0_xboole_0)))),
% 32.10/32.32      inference('demod', [status(thm)], ['5', '8', '9', '10'])).
% 32.10/32.32  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('13', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 32.10/32.32      inference('cnf', [status(esa)], [d2_xboole_0])).
% 32.10/32.32  thf('14', plain, (((sk_A) != (o_0_0_xboole_0))),
% 32.10/32.32      inference('demod', [status(thm)], ['12', '13'])).
% 32.10/32.32  thf('15', plain,
% 32.10/32.32      ((((k2_relat_1 @ sk_D) != (sk_A))
% 32.10/32.32        | ~ (v2_funct_1 @ sk_D)
% 32.10/32.32        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 32.10/32.32      inference('simplify_reflect-', [status(thm)], ['11', '14'])).
% 32.10/32.32  thf('16', plain,
% 32.10/32.32      ((r2_relset_1 @ sk_A @ sk_A @ 
% 32.10/32.32        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 32.10/32.32        (k6_partfun1 @ sk_A))),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('17', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 32.10/32.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 32.10/32.32  thf('18', plain,
% 32.10/32.32      ((r2_relset_1 @ sk_A @ sk_A @ 
% 32.10/32.32        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 32.10/32.32        (k6_relat_1 @ sk_A))),
% 32.10/32.32      inference('demod', [status(thm)], ['16', '17'])).
% 32.10/32.32  thf('19', plain,
% 32.10/32.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('20', plain,
% 32.10/32.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf(dt_k1_partfun1, axiom,
% 32.10/32.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 32.10/32.32     ( ( ( v1_funct_1 @ E ) & 
% 32.10/32.32         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 32.10/32.32         ( v1_funct_1 @ F ) & 
% 32.10/32.32         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 32.10/32.32       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 32.10/32.32         ( m1_subset_1 @
% 32.10/32.32           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 32.10/32.32           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 32.10/32.32  thf('21', plain,
% 32.10/32.32      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 32.10/32.32         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 32.10/32.32          | ~ (v1_funct_1 @ X21)
% 32.10/32.32          | ~ (v1_funct_1 @ X24)
% 32.10/32.32          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 32.10/32.32          | (m1_subset_1 @ (k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24) @ 
% 32.10/32.32             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X26))))),
% 32.10/32.32      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 32.10/32.32  thf('22', plain,
% 32.10/32.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.10/32.32         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 32.10/32.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 32.10/32.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 32.10/32.32          | ~ (v1_funct_1 @ X1)
% 32.10/32.32          | ~ (v1_funct_1 @ sk_C))),
% 32.10/32.32      inference('sup-', [status(thm)], ['20', '21'])).
% 32.10/32.32  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('24', plain,
% 32.10/32.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.10/32.32         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 32.10/32.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 32.10/32.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 32.10/32.32          | ~ (v1_funct_1 @ X1))),
% 32.10/32.32      inference('demod', [status(thm)], ['22', '23'])).
% 32.10/32.32  thf('25', plain,
% 32.10/32.32      ((~ (v1_funct_1 @ sk_D)
% 32.10/32.32        | (m1_subset_1 @ 
% 32.10/32.32           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 32.10/32.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 32.10/32.32      inference('sup-', [status(thm)], ['19', '24'])).
% 32.10/32.32  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('27', plain,
% 32.10/32.32      ((m1_subset_1 @ 
% 32.10/32.32        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 32.10/32.32        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 32.10/32.32      inference('demod', [status(thm)], ['25', '26'])).
% 32.10/32.32  thf(redefinition_r2_relset_1, axiom,
% 32.10/32.32    (![A:$i,B:$i,C:$i,D:$i]:
% 32.10/32.32     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 32.10/32.32         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.10/32.32       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 32.10/32.32  thf('28', plain,
% 32.10/32.32      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 32.10/32.32         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 32.10/32.32          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 32.10/32.32          | ((X17) = (X20))
% 32.10/32.32          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 32.10/32.32      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 32.10/32.32  thf('29', plain,
% 32.10/32.32      (![X0 : $i]:
% 32.10/32.32         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 32.10/32.32             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 32.10/32.32          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 32.10/32.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 32.10/32.32      inference('sup-', [status(thm)], ['27', '28'])).
% 32.10/32.32  thf('30', plain,
% 32.10/32.32      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 32.10/32.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 32.10/32.32        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 32.10/32.32            = (k6_relat_1 @ sk_A)))),
% 32.10/32.32      inference('sup-', [status(thm)], ['18', '29'])).
% 32.10/32.32  thf(dt_k6_partfun1, axiom,
% 32.10/32.32    (![A:$i]:
% 32.10/32.32     ( ( m1_subset_1 @
% 32.10/32.32         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 32.10/32.32       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 32.10/32.32  thf('31', plain,
% 32.10/32.32      (![X28 : $i]:
% 32.10/32.32         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 32.10/32.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 32.10/32.32      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 32.10/32.32  thf('32', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 32.10/32.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 32.10/32.32  thf('33', plain,
% 32.10/32.32      (![X28 : $i]:
% 32.10/32.32         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 32.10/32.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 32.10/32.32      inference('demod', [status(thm)], ['31', '32'])).
% 32.10/32.32  thf('34', plain,
% 32.10/32.32      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 32.10/32.32         = (k6_relat_1 @ sk_A))),
% 32.10/32.32      inference('demod', [status(thm)], ['30', '33'])).
% 32.10/32.32  thf('35', plain,
% 32.10/32.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf(t24_funct_2, axiom,
% 32.10/32.32    (![A:$i,B:$i,C:$i]:
% 32.10/32.32     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 32.10/32.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.10/32.32       ( ![D:$i]:
% 32.10/32.32         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 32.10/32.32             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 32.10/32.32           ( ( r2_relset_1 @
% 32.10/32.32               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 32.10/32.32               ( k6_partfun1 @ B ) ) =>
% 32.10/32.32             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 32.10/32.32  thf('36', plain,
% 32.10/32.32      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 32.10/32.32         (~ (v1_funct_1 @ X36)
% 32.10/32.32          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 32.10/32.32          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 32.10/32.32          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 32.10/32.32               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 32.10/32.32               (k6_partfun1 @ X37))
% 32.10/32.32          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 32.10/32.32          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 32.10/32.32          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 32.10/32.32          | ~ (v1_funct_1 @ X39))),
% 32.10/32.32      inference('cnf', [status(esa)], [t24_funct_2])).
% 32.10/32.32  thf('37', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 32.10/32.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 32.10/32.32  thf('38', plain,
% 32.10/32.32      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 32.10/32.32         (~ (v1_funct_1 @ X36)
% 32.10/32.32          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 32.10/32.32          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 32.10/32.32          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 32.10/32.32               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 32.10/32.32               (k6_relat_1 @ X37))
% 32.10/32.32          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 32.10/32.32          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 32.10/32.32          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 32.10/32.32          | ~ (v1_funct_1 @ X39))),
% 32.10/32.32      inference('demod', [status(thm)], ['36', '37'])).
% 32.10/32.32  thf('39', plain,
% 32.10/32.32      (![X0 : $i]:
% 32.10/32.32         (~ (v1_funct_1 @ X0)
% 32.10/32.32          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 32.10/32.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 32.10/32.32          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 32.10/32.32          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 32.10/32.32               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 32.10/32.32               (k6_relat_1 @ sk_A))
% 32.10/32.32          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 32.10/32.32          | ~ (v1_funct_1 @ sk_C))),
% 32.10/32.32      inference('sup-', [status(thm)], ['35', '38'])).
% 32.10/32.32  thf('40', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('42', plain,
% 32.10/32.32      (![X0 : $i]:
% 32.10/32.32         (~ (v1_funct_1 @ X0)
% 32.10/32.32          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 32.10/32.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 32.10/32.32          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 32.10/32.32          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 32.10/32.32               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 32.10/32.32               (k6_relat_1 @ sk_A)))),
% 32.10/32.32      inference('demod', [status(thm)], ['39', '40', '41'])).
% 32.10/32.32  thf('43', plain,
% 32.10/32.32      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 32.10/32.32           (k6_relat_1 @ sk_A))
% 32.10/32.32        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 32.10/32.32        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 32.10/32.32        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 32.10/32.32        | ~ (v1_funct_1 @ sk_D))),
% 32.10/32.32      inference('sup-', [status(thm)], ['34', '42'])).
% 32.10/32.32  thf('44', plain,
% 32.10/32.32      (![X28 : $i]:
% 32.10/32.32         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 32.10/32.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 32.10/32.32      inference('demod', [status(thm)], ['31', '32'])).
% 32.10/32.32  thf('45', plain,
% 32.10/32.32      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 32.10/32.32         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 32.10/32.32          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 32.10/32.32          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 32.10/32.32          | ((X17) != (X20)))),
% 32.10/32.32      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 32.10/32.32  thf('46', plain,
% 32.10/32.32      (![X18 : $i, X19 : $i, X20 : $i]:
% 32.10/32.32         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 32.10/32.32          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 32.10/32.32      inference('simplify', [status(thm)], ['45'])).
% 32.10/32.32  thf('47', plain,
% 32.10/32.32      (![X0 : $i]:
% 32.10/32.32         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 32.10/32.32      inference('sup-', [status(thm)], ['44', '46'])).
% 32.10/32.32  thf('48', plain,
% 32.10/32.32      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 32.10/32.32      inference('sup-', [status(thm)], ['6', '7'])).
% 32.10/32.32  thf('49', plain,
% 32.10/32.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('50', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('52', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 32.10/32.32      inference('demod', [status(thm)], ['43', '47', '48', '49', '50', '51'])).
% 32.10/32.32  thf('53', plain,
% 32.10/32.32      ((((sk_A) != (sk_A))
% 32.10/32.32        | ~ (v2_funct_1 @ sk_D)
% 32.10/32.32        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 32.10/32.32      inference('demod', [status(thm)], ['15', '52'])).
% 32.10/32.32  thf('54', plain,
% 32.10/32.32      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 32.10/32.32        | ~ (v2_funct_1 @ sk_D))),
% 32.10/32.32      inference('simplify', [status(thm)], ['53'])).
% 32.10/32.32  thf('55', plain,
% 32.10/32.32      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 32.10/32.32         = (k6_relat_1 @ sk_A))),
% 32.10/32.32      inference('demod', [status(thm)], ['30', '33'])).
% 32.10/32.32  thf('56', plain,
% 32.10/32.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf(t30_funct_2, axiom,
% 32.10/32.32    (![A:$i,B:$i,C:$i,D:$i]:
% 32.10/32.32     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 32.10/32.32         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 32.10/32.32       ( ![E:$i]:
% 32.10/32.32         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 32.10/32.32             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 32.10/32.32           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 32.10/32.32               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 32.10/32.32             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 32.10/32.32               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 32.10/32.32  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 32.10/32.32  thf(zf_stmt_2, axiom,
% 32.10/32.32    (![C:$i,B:$i]:
% 32.10/32.32     ( ( zip_tseitin_1 @ C @ B ) =>
% 32.10/32.32       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 32.10/32.32  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 32.10/32.32  thf(zf_stmt_4, axiom,
% 32.10/32.32    (![E:$i,D:$i]:
% 32.10/32.32     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 32.10/32.32  thf(zf_stmt_5, axiom,
% 32.10/32.32    (![A:$i,B:$i,C:$i,D:$i]:
% 32.10/32.32     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 32.10/32.32         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.10/32.32       ( ![E:$i]:
% 32.10/32.32         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 32.10/32.32             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 32.10/32.32           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 32.10/32.32               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 32.10/32.32             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 32.10/32.32  thf('57', plain,
% 32.10/32.32      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 32.10/32.32         (~ (v1_funct_1 @ X44)
% 32.10/32.32          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 32.10/32.32          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 32.10/32.32          | (zip_tseitin_0 @ X44 @ X47)
% 32.10/32.32          | ~ (v2_funct_1 @ (k1_partfun1 @ X48 @ X45 @ X45 @ X46 @ X47 @ X44))
% 32.10/32.32          | (zip_tseitin_1 @ X46 @ X45)
% 32.10/32.32          | ((k2_relset_1 @ X48 @ X45 @ X47) != (X45))
% 32.10/32.32          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X45)))
% 32.10/32.32          | ~ (v1_funct_2 @ X47 @ X48 @ X45)
% 32.10/32.32          | ~ (v1_funct_1 @ X47))),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_5])).
% 32.10/32.32  thf('58', plain,
% 32.10/32.32      (![X0 : $i, X1 : $i]:
% 32.10/32.32         (~ (v1_funct_1 @ X0)
% 32.10/32.32          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 32.10/32.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 32.10/32.32          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 32.10/32.32          | (zip_tseitin_1 @ sk_A @ sk_B)
% 32.10/32.32          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 32.10/32.32          | (zip_tseitin_0 @ sk_D @ X0)
% 32.10/32.32          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 32.10/32.32          | ~ (v1_funct_1 @ sk_D))),
% 32.10/32.32      inference('sup-', [status(thm)], ['56', '57'])).
% 32.10/32.32  thf('59', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('61', plain,
% 32.10/32.32      (![X0 : $i, X1 : $i]:
% 32.10/32.32         (~ (v1_funct_1 @ X0)
% 32.10/32.32          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 32.10/32.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 32.10/32.32          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 32.10/32.32          | (zip_tseitin_1 @ sk_A @ sk_B)
% 32.10/32.32          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 32.10/32.32          | (zip_tseitin_0 @ sk_D @ X0))),
% 32.10/32.32      inference('demod', [status(thm)], ['58', '59', '60'])).
% 32.10/32.32  thf('62', plain,
% 32.10/32.32      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 32.10/32.32        | (zip_tseitin_0 @ sk_D @ sk_C)
% 32.10/32.32        | (zip_tseitin_1 @ sk_A @ sk_B)
% 32.10/32.32        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 32.10/32.32        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 32.10/32.32        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 32.10/32.32        | ~ (v1_funct_1 @ sk_C))),
% 32.10/32.32      inference('sup-', [status(thm)], ['55', '61'])).
% 32.10/32.32  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 32.10/32.32  thf('63', plain, (![X8 : $i]: (v2_funct_1 @ (k6_relat_1 @ X8))),
% 32.10/32.32      inference('cnf', [status(esa)], [t52_funct_1])).
% 32.10/32.32  thf('64', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('65', plain,
% 32.10/32.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('66', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.32  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 32.10/32.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('68', plain,
% 32.10/32.33      (((zip_tseitin_0 @ sk_D @ sk_C)
% 32.10/32.33        | (zip_tseitin_1 @ sk_A @ sk_B)
% 32.10/32.33        | ((sk_B) != (sk_B)))),
% 32.10/32.33      inference('demod', [status(thm)], ['62', '63', '64', '65', '66', '67'])).
% 32.10/32.33  thf('69', plain,
% 32.10/32.33      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 32.10/32.33      inference('simplify', [status(thm)], ['68'])).
% 32.10/32.33  thf('70', plain,
% 32.10/32.33      (![X42 : $i, X43 : $i]:
% 32.10/32.33         (((X42) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X42 @ X43))),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_2])).
% 32.10/32.33  thf('71', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 32.10/32.33      inference('cnf', [status(esa)], [d2_xboole_0])).
% 32.10/32.33  thf('72', plain,
% 32.10/32.33      (![X42 : $i, X43 : $i]:
% 32.10/32.33         (((X42) = (o_0_0_xboole_0)) | ~ (zip_tseitin_1 @ X42 @ X43))),
% 32.10/32.33      inference('demod', [status(thm)], ['70', '71'])).
% 32.10/32.33  thf('73', plain,
% 32.10/32.33      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (o_0_0_xboole_0)))),
% 32.10/32.33      inference('sup-', [status(thm)], ['69', '72'])).
% 32.10/32.33  thf('74', plain, (((sk_A) != (o_0_0_xboole_0))),
% 32.10/32.33      inference('demod', [status(thm)], ['12', '13'])).
% 32.10/32.33  thf('75', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 32.10/32.33      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 32.10/32.33  thf('76', plain,
% 32.10/32.33      (![X40 : $i, X41 : $i]:
% 32.10/32.33         ((v2_funct_1 @ X41) | ~ (zip_tseitin_0 @ X41 @ X40))),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_4])).
% 32.10/32.33  thf('77', plain, ((v2_funct_1 @ sk_D)),
% 32.10/32.33      inference('sup-', [status(thm)], ['75', '76'])).
% 32.10/32.33  thf('78', plain,
% 32.10/32.33      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 32.10/32.33      inference('demod', [status(thm)], ['54', '77'])).
% 32.10/32.33  thf(t58_funct_1, axiom,
% 32.10/32.33    (![A:$i]:
% 32.10/32.33     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 32.10/32.33       ( ( v2_funct_1 @ A ) =>
% 32.10/32.33         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 32.10/32.33             ( k1_relat_1 @ A ) ) & 
% 32.10/32.33           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 32.10/32.33             ( k1_relat_1 @ A ) ) ) ) ))).
% 32.10/32.33  thf('79', plain,
% 32.10/32.33      (![X10 : $i]:
% 32.10/32.33         (~ (v2_funct_1 @ X10)
% 32.10/32.33          | ((k2_relat_1 @ (k5_relat_1 @ X10 @ (k2_funct_1 @ X10)))
% 32.10/32.33              = (k1_relat_1 @ X10))
% 32.10/32.33          | ~ (v1_funct_1 @ X10)
% 32.10/32.33          | ~ (v1_relat_1 @ X10))),
% 32.10/32.33      inference('cnf', [status(esa)], [t58_funct_1])).
% 32.10/32.33  thf('80', plain,
% 32.10/32.33      ((((k2_relat_1 @ (k6_relat_1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 32.10/32.33        | ~ (v1_relat_1 @ sk_D)
% 32.10/32.33        | ~ (v1_funct_1 @ sk_D)
% 32.10/32.33        | ~ (v2_funct_1 @ sk_D))),
% 32.10/32.33      inference('sup+', [status(thm)], ['78', '79'])).
% 32.10/32.33  thf(t71_relat_1, axiom,
% 32.10/32.33    (![A:$i]:
% 32.10/32.33     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 32.10/32.33       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 32.10/32.33  thf('81', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 32.10/32.33      inference('cnf', [status(esa)], [t71_relat_1])).
% 32.10/32.33  thf('82', plain,
% 32.10/32.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf(cc1_relset_1, axiom,
% 32.10/32.33    (![A:$i,B:$i,C:$i]:
% 32.10/32.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.10/32.33       ( v1_relat_1 @ C ) ))).
% 32.10/32.33  thf('83', plain,
% 32.10/32.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 32.10/32.33         ((v1_relat_1 @ X11)
% 32.10/32.33          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 32.10/32.33      inference('cnf', [status(esa)], [cc1_relset_1])).
% 32.10/32.33  thf('84', plain, ((v1_relat_1 @ sk_D)),
% 32.10/32.33      inference('sup-', [status(thm)], ['82', '83'])).
% 32.10/32.33  thf('85', plain, ((v1_funct_1 @ sk_D)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('86', plain, ((v2_funct_1 @ sk_D)),
% 32.10/32.33      inference('sup-', [status(thm)], ['75', '76'])).
% 32.10/32.33  thf('87', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 32.10/32.33      inference('demod', [status(thm)], ['80', '81', '84', '85', '86'])).
% 32.10/32.33  thf(t78_relat_1, axiom,
% 32.10/32.33    (![A:$i]:
% 32.10/32.33     ( ( v1_relat_1 @ A ) =>
% 32.10/32.33       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 32.10/32.33  thf('88', plain,
% 32.10/32.33      (![X5 : $i]:
% 32.10/32.33         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 32.10/32.33          | ~ (v1_relat_1 @ X5))),
% 32.10/32.33      inference('cnf', [status(esa)], [t78_relat_1])).
% 32.10/32.33  thf('89', plain,
% 32.10/32.33      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (sk_D))
% 32.10/32.33        | ~ (v1_relat_1 @ sk_D))),
% 32.10/32.33      inference('sup+', [status(thm)], ['87', '88'])).
% 32.10/32.33  thf('90', plain,
% 32.10/32.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('91', plain,
% 32.10/32.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf(redefinition_k1_partfun1, axiom,
% 32.10/32.33    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 32.10/32.33     ( ( ( v1_funct_1 @ E ) & 
% 32.10/32.33         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 32.10/32.33         ( v1_funct_1 @ F ) & 
% 32.10/32.33         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 32.10/32.33       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 32.10/32.33  thf('92', plain,
% 32.10/32.33      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 32.10/32.33         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 32.10/32.33          | ~ (v1_funct_1 @ X29)
% 32.10/32.33          | ~ (v1_funct_1 @ X32)
% 32.10/32.33          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 32.10/32.33          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 32.10/32.33              = (k5_relat_1 @ X29 @ X32)))),
% 32.10/32.33      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 32.10/32.33  thf('93', plain,
% 32.10/32.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.10/32.33         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 32.10/32.33            = (k5_relat_1 @ sk_C @ X0))
% 32.10/32.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 32.10/32.33          | ~ (v1_funct_1 @ X0)
% 32.10/32.33          | ~ (v1_funct_1 @ sk_C))),
% 32.10/32.33      inference('sup-', [status(thm)], ['91', '92'])).
% 32.10/32.33  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('95', plain,
% 32.10/32.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.10/32.33         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 32.10/32.33            = (k5_relat_1 @ sk_C @ X0))
% 32.10/32.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 32.10/32.33          | ~ (v1_funct_1 @ X0))),
% 32.10/32.33      inference('demod', [status(thm)], ['93', '94'])).
% 32.10/32.33  thf('96', plain,
% 32.10/32.33      ((~ (v1_funct_1 @ sk_D)
% 32.10/32.33        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 32.10/32.33            = (k5_relat_1 @ sk_C @ sk_D)))),
% 32.10/32.33      inference('sup-', [status(thm)], ['90', '95'])).
% 32.10/32.33  thf('97', plain, ((v1_funct_1 @ sk_D)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('98', plain,
% 32.10/32.33      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 32.10/32.33         = (k6_relat_1 @ sk_A))),
% 32.10/32.33      inference('demod', [status(thm)], ['30', '33'])).
% 32.10/32.33  thf('99', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 32.10/32.33      inference('demod', [status(thm)], ['96', '97', '98'])).
% 32.10/32.33  thf(dt_k2_funct_1, axiom,
% 32.10/32.33    (![A:$i]:
% 32.10/32.33     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 32.10/32.33       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 32.10/32.33         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 32.10/32.33  thf('100', plain,
% 32.10/32.33      (![X7 : $i]:
% 32.10/32.33         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 32.10/32.33          | ~ (v1_funct_1 @ X7)
% 32.10/32.33          | ~ (v1_relat_1 @ X7))),
% 32.10/32.33      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 32.10/32.33  thf('101', plain,
% 32.10/32.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('102', plain,
% 32.10/32.33      (![X49 : $i, X50 : $i, X51 : $i]:
% 32.10/32.33         (((X49) = (k1_xboole_0))
% 32.10/32.33          | ~ (v1_funct_1 @ X50)
% 32.10/32.33          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 32.10/32.33          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 32.10/32.33          | ((k5_relat_1 @ (k2_funct_1 @ X50) @ X50) = (k6_partfun1 @ X49))
% 32.10/32.33          | ~ (v2_funct_1 @ X50)
% 32.10/32.33          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 32.10/32.33      inference('cnf', [status(esa)], [t35_funct_2])).
% 32.10/32.33  thf('103', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 32.10/32.33      inference('cnf', [status(esa)], [d2_xboole_0])).
% 32.10/32.33  thf('104', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 32.10/32.33      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 32.10/32.33  thf('105', plain,
% 32.10/32.33      (![X49 : $i, X50 : $i, X51 : $i]:
% 32.10/32.33         (((X49) = (o_0_0_xboole_0))
% 32.10/32.33          | ~ (v1_funct_1 @ X50)
% 32.10/32.33          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 32.10/32.33          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 32.10/32.33          | ((k5_relat_1 @ (k2_funct_1 @ X50) @ X50) = (k6_relat_1 @ X49))
% 32.10/32.33          | ~ (v2_funct_1 @ X50)
% 32.10/32.33          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 32.10/32.33      inference('demod', [status(thm)], ['102', '103', '104'])).
% 32.10/32.33  thf('106', plain,
% 32.10/32.33      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 32.10/32.33        | ~ (v2_funct_1 @ sk_C)
% 32.10/32.33        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 32.10/32.33        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 32.10/32.33        | ~ (v1_funct_1 @ sk_C)
% 32.10/32.33        | ((sk_B) = (o_0_0_xboole_0)))),
% 32.10/32.33      inference('sup-', [status(thm)], ['101', '105'])).
% 32.10/32.33  thf('107', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('109', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('111', plain,
% 32.10/32.33      ((((sk_B) != (sk_B))
% 32.10/32.33        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 32.10/32.33        | ((sk_B) = (o_0_0_xboole_0)))),
% 32.10/32.33      inference('demod', [status(thm)], ['106', '107', '108', '109', '110'])).
% 32.10/32.33  thf('112', plain,
% 32.10/32.33      ((((sk_B) = (o_0_0_xboole_0))
% 32.10/32.33        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 32.10/32.33      inference('simplify', [status(thm)], ['111'])).
% 32.10/32.33  thf('113', plain, (((sk_B) != (k1_xboole_0))),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('114', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 32.10/32.33      inference('cnf', [status(esa)], [d2_xboole_0])).
% 32.10/32.33  thf('115', plain, (((sk_B) != (o_0_0_xboole_0))),
% 32.10/32.33      inference('demod', [status(thm)], ['113', '114'])).
% 32.10/32.33  thf('116', plain,
% 32.10/32.33      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 32.10/32.33      inference('simplify_reflect-', [status(thm)], ['112', '115'])).
% 32.10/32.33  thf(t55_relat_1, axiom,
% 32.10/32.33    (![A:$i]:
% 32.10/32.33     ( ( v1_relat_1 @ A ) =>
% 32.10/32.33       ( ![B:$i]:
% 32.10/32.33         ( ( v1_relat_1 @ B ) =>
% 32.10/32.33           ( ![C:$i]:
% 32.10/32.33             ( ( v1_relat_1 @ C ) =>
% 32.10/32.33               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 32.10/32.33                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 32.10/32.33  thf('117', plain,
% 32.10/32.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.10/32.33         (~ (v1_relat_1 @ X0)
% 32.10/32.33          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 32.10/32.33              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 32.10/32.33          | ~ (v1_relat_1 @ X2)
% 32.10/32.33          | ~ (v1_relat_1 @ X1))),
% 32.10/32.33      inference('cnf', [status(esa)], [t55_relat_1])).
% 32.10/32.33  thf('118', plain,
% 32.10/32.33      (![X0 : $i]:
% 32.10/32.33         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 32.10/32.33            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 32.10/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 32.10/32.33          | ~ (v1_relat_1 @ X0)
% 32.10/32.33          | ~ (v1_relat_1 @ sk_C))),
% 32.10/32.33      inference('sup+', [status(thm)], ['116', '117'])).
% 32.10/32.33  thf('119', plain,
% 32.10/32.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('120', plain,
% 32.10/32.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 32.10/32.33         ((v1_relat_1 @ X11)
% 32.10/32.33          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 32.10/32.33      inference('cnf', [status(esa)], [cc1_relset_1])).
% 32.10/32.33  thf('121', plain, ((v1_relat_1 @ sk_C)),
% 32.10/32.33      inference('sup-', [status(thm)], ['119', '120'])).
% 32.10/32.33  thf('122', plain,
% 32.10/32.33      (![X0 : $i]:
% 32.10/32.33         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 32.10/32.33            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 32.10/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 32.10/32.33          | ~ (v1_relat_1 @ X0))),
% 32.10/32.33      inference('demod', [status(thm)], ['118', '121'])).
% 32.10/32.33  thf('123', plain,
% 32.10/32.33      (![X0 : $i]:
% 32.10/32.33         (~ (v1_relat_1 @ sk_C)
% 32.10/32.33          | ~ (v1_funct_1 @ sk_C)
% 32.10/32.33          | ~ (v1_relat_1 @ X0)
% 32.10/32.33          | ((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 32.10/32.33              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 32.10/32.33      inference('sup-', [status(thm)], ['100', '122'])).
% 32.10/32.33  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 32.10/32.33      inference('sup-', [status(thm)], ['119', '120'])).
% 32.10/32.33  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('126', plain,
% 32.10/32.33      (![X0 : $i]:
% 32.10/32.33         (~ (v1_relat_1 @ X0)
% 32.10/32.33          | ((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 32.10/32.33              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 32.10/32.33      inference('demod', [status(thm)], ['123', '124', '125'])).
% 32.10/32.33  thf('127', plain,
% 32.10/32.33      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D)
% 32.10/32.33          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 32.10/32.33        | ~ (v1_relat_1 @ sk_D))),
% 32.10/32.33      inference('sup+', [status(thm)], ['99', '126'])).
% 32.10/32.33  thf('128', plain,
% 32.10/32.33      (![X7 : $i]:
% 32.10/32.33         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 32.10/32.33          | ~ (v1_funct_1 @ X7)
% 32.10/32.33          | ~ (v1_relat_1 @ X7))),
% 32.10/32.33      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 32.10/32.33  thf(t55_funct_1, axiom,
% 32.10/32.33    (![A:$i]:
% 32.10/32.33     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 32.10/32.33       ( ( v2_funct_1 @ A ) =>
% 32.10/32.33         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 32.10/32.33           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 32.10/32.33  thf('129', plain,
% 32.10/32.33      (![X9 : $i]:
% 32.10/32.33         (~ (v2_funct_1 @ X9)
% 32.10/32.33          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 32.10/32.33          | ~ (v1_funct_1 @ X9)
% 32.10/32.33          | ~ (v1_relat_1 @ X9))),
% 32.10/32.33      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.10/32.33  thf(t80_relat_1, axiom,
% 32.10/32.33    (![A:$i]:
% 32.10/32.33     ( ( v1_relat_1 @ A ) =>
% 32.10/32.33       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 32.10/32.33  thf('130', plain,
% 32.10/32.33      (![X6 : $i]:
% 32.10/32.33         (((k5_relat_1 @ X6 @ (k6_relat_1 @ (k2_relat_1 @ X6))) = (X6))
% 32.10/32.33          | ~ (v1_relat_1 @ X6))),
% 32.10/32.33      inference('cnf', [status(esa)], [t80_relat_1])).
% 32.10/32.33  thf('131', plain,
% 32.10/32.33      (![X0 : $i]:
% 32.10/32.33         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 32.10/32.33            = (k2_funct_1 @ X0))
% 32.10/32.33          | ~ (v1_relat_1 @ X0)
% 32.10/32.33          | ~ (v1_funct_1 @ X0)
% 32.10/32.33          | ~ (v2_funct_1 @ X0)
% 32.10/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 32.10/32.33      inference('sup+', [status(thm)], ['129', '130'])).
% 32.10/32.33  thf('132', plain,
% 32.10/32.33      (![X0 : $i]:
% 32.10/32.33         (~ (v1_relat_1 @ X0)
% 32.10/32.33          | ~ (v1_funct_1 @ X0)
% 32.10/32.33          | ~ (v2_funct_1 @ X0)
% 32.10/32.33          | ~ (v1_funct_1 @ X0)
% 32.10/32.33          | ~ (v1_relat_1 @ X0)
% 32.10/32.33          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 32.10/32.33              = (k2_funct_1 @ X0)))),
% 32.10/32.33      inference('sup-', [status(thm)], ['128', '131'])).
% 32.10/32.33  thf('133', plain,
% 32.10/32.33      (![X0 : $i]:
% 32.10/32.33         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 32.10/32.33            = (k2_funct_1 @ X0))
% 32.10/32.33          | ~ (v2_funct_1 @ X0)
% 32.10/32.33          | ~ (v1_funct_1 @ X0)
% 32.10/32.33          | ~ (v1_relat_1 @ X0))),
% 32.10/32.33      inference('simplify', [status(thm)], ['132'])).
% 32.10/32.33  thf('134', plain,
% 32.10/32.33      (![X7 : $i]:
% 32.10/32.33         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 32.10/32.33          | ~ (v1_funct_1 @ X7)
% 32.10/32.33          | ~ (v1_relat_1 @ X7))),
% 32.10/32.33      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 32.10/32.33  thf('135', plain,
% 32.10/32.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('136', plain,
% 32.10/32.33      (![X14 : $i, X15 : $i, X16 : $i]:
% 32.10/32.33         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 32.10/32.33          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 32.10/32.33      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 32.10/32.33  thf('137', plain,
% 32.10/32.33      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 32.10/32.33      inference('sup-', [status(thm)], ['135', '136'])).
% 32.10/32.33  thf('138', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('139', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 32.10/32.33      inference('sup+', [status(thm)], ['137', '138'])).
% 32.10/32.33  thf('140', plain,
% 32.10/32.33      (![X7 : $i]:
% 32.10/32.33         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 32.10/32.33          | ~ (v1_funct_1 @ X7)
% 32.10/32.33          | ~ (v1_relat_1 @ X7))),
% 32.10/32.33      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 32.10/32.33  thf('141', plain,
% 32.10/32.33      (![X9 : $i]:
% 32.10/32.33         (~ (v2_funct_1 @ X9)
% 32.10/32.33          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 32.10/32.33          | ~ (v1_funct_1 @ X9)
% 32.10/32.33          | ~ (v1_relat_1 @ X9))),
% 32.10/32.33      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.10/32.33  thf('142', plain,
% 32.10/32.33      (![X5 : $i]:
% 32.10/32.33         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 32.10/32.33          | ~ (v1_relat_1 @ X5))),
% 32.10/32.33      inference('cnf', [status(esa)], [t78_relat_1])).
% 32.10/32.33  thf('143', plain,
% 32.10/32.33      (![X0 : $i]:
% 32.10/32.33         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 32.10/32.33            = (k2_funct_1 @ X0))
% 32.10/32.33          | ~ (v1_relat_1 @ X0)
% 32.10/32.33          | ~ (v1_funct_1 @ X0)
% 32.10/32.33          | ~ (v2_funct_1 @ X0)
% 32.10/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 32.10/32.33      inference('sup+', [status(thm)], ['141', '142'])).
% 32.10/32.33  thf('144', plain,
% 32.10/32.33      (![X0 : $i]:
% 32.10/32.33         (~ (v1_relat_1 @ X0)
% 32.10/32.33          | ~ (v1_funct_1 @ X0)
% 32.10/32.33          | ~ (v2_funct_1 @ X0)
% 32.10/32.33          | ~ (v1_funct_1 @ X0)
% 32.10/32.33          | ~ (v1_relat_1 @ X0)
% 32.10/32.33          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 32.10/32.33              = (k2_funct_1 @ X0)))),
% 32.10/32.33      inference('sup-', [status(thm)], ['140', '143'])).
% 32.10/32.33  thf('145', plain,
% 32.10/32.33      (![X0 : $i]:
% 32.10/32.33         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 32.10/32.33            = (k2_funct_1 @ X0))
% 32.10/32.33          | ~ (v2_funct_1 @ X0)
% 32.10/32.33          | ~ (v1_funct_1 @ X0)
% 32.10/32.33          | ~ (v1_relat_1 @ X0))),
% 32.10/32.33      inference('simplify', [status(thm)], ['144'])).
% 32.10/32.33  thf('146', plain,
% 32.10/32.33      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 32.10/32.33          = (k2_funct_1 @ sk_C))
% 32.10/32.33        | ~ (v1_relat_1 @ sk_C)
% 32.10/32.33        | ~ (v1_funct_1 @ sk_C)
% 32.10/32.33        | ~ (v2_funct_1 @ sk_C))),
% 32.10/32.33      inference('sup+', [status(thm)], ['139', '145'])).
% 32.10/32.33  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 32.10/32.33      inference('sup-', [status(thm)], ['119', '120'])).
% 32.10/32.33  thf('148', plain, ((v1_funct_1 @ sk_C)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('149', plain, ((v2_funct_1 @ sk_C)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('150', plain,
% 32.10/32.33      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 32.10/32.33         = (k2_funct_1 @ sk_C))),
% 32.10/32.33      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 32.10/32.33  thf('151', plain,
% 32.10/32.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.10/32.33         (~ (v1_relat_1 @ X0)
% 32.10/32.33          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 32.10/32.33              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 32.10/32.33          | ~ (v1_relat_1 @ X2)
% 32.10/32.33          | ~ (v1_relat_1 @ X1))),
% 32.10/32.33      inference('cnf', [status(esa)], [t55_relat_1])).
% 32.10/32.33  thf('152', plain,
% 32.10/32.33      (![X0 : $i]:
% 32.10/32.33         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 32.10/32.33            = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 32.10/32.33               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 32.10/32.33          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 32.10/32.33          | ~ (v1_relat_1 @ X0)
% 32.10/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 32.10/32.33      inference('sup+', [status(thm)], ['150', '151'])).
% 32.10/32.33  thf('153', plain,
% 32.10/32.33      (![X28 : $i]:
% 32.10/32.33         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 32.10/32.33          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 32.10/32.33      inference('demod', [status(thm)], ['31', '32'])).
% 32.10/32.33  thf('154', plain,
% 32.10/32.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 32.10/32.33         ((v1_relat_1 @ X11)
% 32.10/32.33          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 32.10/32.33      inference('cnf', [status(esa)], [cc1_relset_1])).
% 32.10/32.33  thf('155', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 32.10/32.33      inference('sup-', [status(thm)], ['153', '154'])).
% 32.10/32.33  thf('156', plain,
% 32.10/32.33      (![X0 : $i]:
% 32.10/32.33         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 32.10/32.33            = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 32.10/32.33               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 32.10/32.33          | ~ (v1_relat_1 @ X0)
% 32.10/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 32.10/32.33      inference('demod', [status(thm)], ['152', '155'])).
% 32.10/32.33  thf('157', plain,
% 32.10/32.33      (![X0 : $i]:
% 32.10/32.33         (~ (v1_relat_1 @ sk_C)
% 32.10/32.33          | ~ (v1_funct_1 @ sk_C)
% 32.10/32.33          | ~ (v1_relat_1 @ X0)
% 32.10/32.33          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 32.10/32.33              = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 32.10/32.33                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 32.10/32.33      inference('sup-', [status(thm)], ['134', '156'])).
% 32.10/32.33  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 32.10/32.33      inference('sup-', [status(thm)], ['119', '120'])).
% 32.10/32.33  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('160', plain,
% 32.10/32.33      (![X0 : $i]:
% 32.10/32.33         (~ (v1_relat_1 @ X0)
% 32.10/32.33          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 32.10/32.33              = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 32.10/32.33                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 32.10/32.33      inference('demod', [status(thm)], ['157', '158', '159'])).
% 32.10/32.33  thf('161', plain,
% 32.10/32.33      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 32.10/32.33          = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 32.10/32.33        | ~ (v1_relat_1 @ sk_C)
% 32.10/32.33        | ~ (v1_funct_1 @ sk_C)
% 32.10/32.33        | ~ (v2_funct_1 @ sk_C)
% 32.10/32.33        | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_C))))),
% 32.10/32.33      inference('sup+', [status(thm)], ['133', '160'])).
% 32.10/32.33  thf('162', plain,
% 32.10/32.33      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 32.10/32.33         = (k2_funct_1 @ sk_C))),
% 32.10/32.33      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 32.10/32.33  thf('163', plain, ((v1_relat_1 @ sk_C)),
% 32.10/32.33      inference('sup-', [status(thm)], ['119', '120'])).
% 32.10/32.33  thf('164', plain, ((v1_funct_1 @ sk_C)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('165', plain, ((v2_funct_1 @ sk_C)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('166', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 32.10/32.33      inference('sup-', [status(thm)], ['153', '154'])).
% 32.10/32.33  thf('167', plain,
% 32.10/32.33      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 32.10/32.33         = (k2_funct_1 @ sk_C))),
% 32.10/32.33      inference('demod', [status(thm)],
% 32.10/32.33                ['161', '162', '163', '164', '165', '166'])).
% 32.10/32.33  thf('168', plain,
% 32.10/32.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('169', plain,
% 32.10/32.33      (![X49 : $i, X50 : $i, X51 : $i]:
% 32.10/32.33         (((X49) = (o_0_0_xboole_0))
% 32.10/32.33          | ~ (v1_funct_1 @ X50)
% 32.10/32.33          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 32.10/32.33          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 32.10/32.33          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_relat_1 @ X51))
% 32.10/32.33          | ~ (v2_funct_1 @ X50)
% 32.10/32.33          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 32.10/32.33      inference('demod', [status(thm)], ['1', '2', '3'])).
% 32.10/32.33  thf('170', plain,
% 32.10/32.33      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 32.10/32.33        | ~ (v2_funct_1 @ sk_C)
% 32.10/32.33        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 32.10/32.33        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 32.10/32.33        | ~ (v1_funct_1 @ sk_C)
% 32.10/32.33        | ((sk_B) = (o_0_0_xboole_0)))),
% 32.10/32.33      inference('sup-', [status(thm)], ['168', '169'])).
% 32.10/32.33  thf('171', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('172', plain, ((v2_funct_1 @ sk_C)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('173', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('175', plain,
% 32.10/32.33      ((((sk_B) != (sk_B))
% 32.10/32.33        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 32.10/32.33        | ((sk_B) = (o_0_0_xboole_0)))),
% 32.10/32.33      inference('demod', [status(thm)], ['170', '171', '172', '173', '174'])).
% 32.10/32.33  thf('176', plain,
% 32.10/32.33      ((((sk_B) = (o_0_0_xboole_0))
% 32.10/32.33        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 32.10/32.33      inference('simplify', [status(thm)], ['175'])).
% 32.10/32.33  thf('177', plain, (((sk_B) != (o_0_0_xboole_0))),
% 32.10/32.33      inference('demod', [status(thm)], ['113', '114'])).
% 32.10/32.33  thf('178', plain,
% 32.10/32.33      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 32.10/32.33      inference('simplify_reflect-', [status(thm)], ['176', '177'])).
% 32.10/32.33  thf('179', plain,
% 32.10/32.33      (![X10 : $i]:
% 32.10/32.33         (~ (v2_funct_1 @ X10)
% 32.10/32.33          | ((k2_relat_1 @ (k5_relat_1 @ X10 @ (k2_funct_1 @ X10)))
% 32.10/32.33              = (k1_relat_1 @ X10))
% 32.10/32.33          | ~ (v1_funct_1 @ X10)
% 32.10/32.33          | ~ (v1_relat_1 @ X10))),
% 32.10/32.33      inference('cnf', [status(esa)], [t58_funct_1])).
% 32.10/32.33  thf('180', plain,
% 32.10/32.33      ((((k2_relat_1 @ (k6_relat_1 @ sk_A)) = (k1_relat_1 @ sk_C))
% 32.10/32.33        | ~ (v1_relat_1 @ sk_C)
% 32.10/32.33        | ~ (v1_funct_1 @ sk_C)
% 32.10/32.33        | ~ (v2_funct_1 @ sk_C))),
% 32.10/32.33      inference('sup+', [status(thm)], ['178', '179'])).
% 32.10/32.33  thf('181', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 32.10/32.33      inference('cnf', [status(esa)], [t71_relat_1])).
% 32.10/32.33  thf('182', plain, ((v1_relat_1 @ sk_C)),
% 32.10/32.33      inference('sup-', [status(thm)], ['119', '120'])).
% 32.10/32.33  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('184', plain, ((v2_funct_1 @ sk_C)),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('185', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 32.10/32.33      inference('demod', [status(thm)], ['180', '181', '182', '183', '184'])).
% 32.10/32.33  thf('186', plain,
% 32.10/32.33      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A))
% 32.10/32.33         = (k2_funct_1 @ sk_C))),
% 32.10/32.33      inference('demod', [status(thm)], ['167', '185'])).
% 32.10/32.33  thf('187', plain, ((v1_relat_1 @ sk_D)),
% 32.10/32.33      inference('sup-', [status(thm)], ['82', '83'])).
% 32.10/32.33  thf('188', plain,
% 32.10/32.33      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 32.10/32.33      inference('demod', [status(thm)], ['127', '186', '187'])).
% 32.10/32.33  thf('189', plain, ((v1_relat_1 @ sk_D)),
% 32.10/32.33      inference('sup-', [status(thm)], ['82', '83'])).
% 32.10/32.33  thf('190', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 32.10/32.33      inference('demod', [status(thm)], ['89', '188', '189'])).
% 32.10/32.33  thf('191', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 32.10/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.10/32.33  thf('192', plain, ($false),
% 32.10/32.33      inference('simplify_reflect-', [status(thm)], ['190', '191'])).
% 32.10/32.33  
% 32.10/32.33  % SZS output end Refutation
% 32.10/32.33  
% 32.15/32.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
