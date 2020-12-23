%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.huneitw2Sc

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:04 EST 2020

% Result     : Theorem 43.02s
% Output     : Refutation 43.02s
% Verified   : 
% Statistics : Number of formulae       :  245 ( 611 expanded)
%              Number of leaves         :   49 ( 203 expanded)
%              Depth                    :   21
%              Number of atoms          : 2420 (13984 expanded)
%              Number of equality atoms :  173 ( 991 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

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

thf('3',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ X50 @ ( k2_funct_1 @ X50 ) )
        = ( k6_partfun1 @ X51 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','7','8','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','13'])).

thf('15',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('28',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('29',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
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

thf('33',plain,(
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

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('41',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['38','42','43','44','45','46'])).

thf('48',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','47'])).

thf('49',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('51',plain,(
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

thf('52',plain,(
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

thf('53',plain,(
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
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('58',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('59',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('60',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X9 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['57','60','61','62','63','64'])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('68',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('69',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X42 = o_0_0_xboole_0 )
      | ~ ( zip_tseitin_1 @ X42 @ X43 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('72',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v2_funct_1 @ X41 )
      | ~ ( zip_tseitin_0 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('74',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['49','74'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('76',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('77',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('78',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('79',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('80',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('82',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('83',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['72','73'])).

thf('86',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','80','83','84','85'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('87',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('88',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('89',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
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

thf('93',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('100',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('101',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
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

thf('104',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('105',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X50 ) @ X50 )
        = ( k6_partfun1 @ X49 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','105'])).

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
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107','108','109','110'])).

thf('112',plain,
    ( ( sk_B = o_0_0_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
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
    = ( k6_partfun1 @ sk_B ) ),
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
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
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
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['101','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['100','126'])).

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
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('132',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ X6 @ ( k6_partfun1 @ ( k2_relat_1 @ X6 ) ) )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['129','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('139',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('143',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('144',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['142','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['141','147'])).

thf('149',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('150',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['148','149','150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('156',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('157',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['154','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['136','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('161',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['135','162'])).

thf('164',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['148','149','150','151'])).

thf('165',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('166',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('169',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['163','164','165','166','167','168'])).

thf('170',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ X50 @ ( k2_funct_1 @ X50 ) )
        = ( k6_partfun1 @ X51 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('172',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['172','173','174','175','176'])).

thf('178',plain,
    ( ( sk_B = o_0_0_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    sk_B != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['113','114'])).

thf('180',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('182',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('184',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('185',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['182','183','184','185','186'])).

thf('188',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['169','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['81','82'])).

thf('190',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','188','189'])).

thf('191',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['81','82'])).

thf('192',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['90','190','191'])).

thf('193',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['192','193'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.huneitw2Sc
% 0.12/0.36  % Computer   : n006.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 12:12:38 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.22/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 43.02/43.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 43.02/43.21  % Solved by: fo/fo7.sh
% 43.02/43.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 43.02/43.21  % done 6483 iterations in 42.738s
% 43.02/43.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 43.02/43.21  % SZS output start Refutation
% 43.02/43.21  thf(sk_D_type, type, sk_D: $i).
% 43.02/43.21  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 43.02/43.21  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 43.02/43.21  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 43.02/43.21  thf(sk_B_type, type, sk_B: $i).
% 43.02/43.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 43.02/43.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 43.02/43.21  thf(sk_C_type, type, sk_C: $i).
% 43.02/43.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 43.02/43.21  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 43.02/43.21  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 43.02/43.21  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 43.02/43.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 43.02/43.21  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 43.02/43.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 43.02/43.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 43.02/43.21  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 43.02/43.21  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 43.02/43.21  thf(sk_A_type, type, sk_A: $i).
% 43.02/43.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 43.02/43.21  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 43.02/43.21  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 43.02/43.21  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 43.02/43.21  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 43.02/43.21  thf(t36_funct_2, conjecture,
% 43.02/43.21    (![A:$i,B:$i,C:$i]:
% 43.02/43.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 43.02/43.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 43.02/43.21       ( ![D:$i]:
% 43.02/43.21         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 43.02/43.21             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 43.02/43.21           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 43.02/43.21               ( r2_relset_1 @
% 43.02/43.21                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 43.02/43.21                 ( k6_partfun1 @ A ) ) & 
% 43.02/43.21               ( v2_funct_1 @ C ) ) =>
% 43.02/43.21             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 43.02/43.21               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 43.02/43.21  thf(zf_stmt_0, negated_conjecture,
% 43.02/43.21    (~( ![A:$i,B:$i,C:$i]:
% 43.02/43.21        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 43.02/43.21            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 43.02/43.21          ( ![D:$i]:
% 43.02/43.21            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 43.02/43.21                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 43.02/43.21              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 43.02/43.21                  ( r2_relset_1 @
% 43.02/43.21                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 43.02/43.21                    ( k6_partfun1 @ A ) ) & 
% 43.02/43.21                  ( v2_funct_1 @ C ) ) =>
% 43.02/43.21                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 43.02/43.21                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 43.02/43.21    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 43.02/43.21  thf('0', plain,
% 43.02/43.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf(t35_funct_2, axiom,
% 43.02/43.21    (![A:$i,B:$i,C:$i]:
% 43.02/43.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 43.02/43.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 43.02/43.21       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 43.02/43.21         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 43.02/43.21           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 43.02/43.21             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 43.02/43.21  thf('1', plain,
% 43.02/43.21      (![X49 : $i, X50 : $i, X51 : $i]:
% 43.02/43.21         (((X49) = (k1_xboole_0))
% 43.02/43.21          | ~ (v1_funct_1 @ X50)
% 43.02/43.21          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 43.02/43.21          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 43.02/43.21          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_partfun1 @ X51))
% 43.02/43.21          | ~ (v2_funct_1 @ X50)
% 43.02/43.21          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 43.02/43.21      inference('cnf', [status(esa)], [t35_funct_2])).
% 43.02/43.21  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 43.02/43.21  thf('2', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 43.02/43.21      inference('cnf', [status(esa)], [d2_xboole_0])).
% 43.02/43.21  thf('3', plain,
% 43.02/43.21      (![X49 : $i, X50 : $i, X51 : $i]:
% 43.02/43.21         (((X49) = (o_0_0_xboole_0))
% 43.02/43.21          | ~ (v1_funct_1 @ X50)
% 43.02/43.21          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 43.02/43.21          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 43.02/43.21          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_partfun1 @ X51))
% 43.02/43.21          | ~ (v2_funct_1 @ X50)
% 43.02/43.21          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 43.02/43.21      inference('demod', [status(thm)], ['1', '2'])).
% 43.02/43.21  thf('4', plain,
% 43.02/43.21      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 43.02/43.21        | ~ (v2_funct_1 @ sk_D)
% 43.02/43.21        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 43.02/43.21        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 43.02/43.21        | ~ (v1_funct_1 @ sk_D)
% 43.02/43.21        | ((sk_A) = (o_0_0_xboole_0)))),
% 43.02/43.21      inference('sup-', [status(thm)], ['0', '3'])).
% 43.02/43.21  thf('5', plain,
% 43.02/43.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf(redefinition_k2_relset_1, axiom,
% 43.02/43.21    (![A:$i,B:$i,C:$i]:
% 43.02/43.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 43.02/43.21       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 43.02/43.21  thf('6', plain,
% 43.02/43.21      (![X15 : $i, X16 : $i, X17 : $i]:
% 43.02/43.21         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 43.02/43.21          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 43.02/43.21      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 43.02/43.21  thf('7', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 43.02/43.21      inference('sup-', [status(thm)], ['5', '6'])).
% 43.02/43.21  thf('8', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('10', plain,
% 43.02/43.21      ((((k2_relat_1 @ sk_D) != (sk_A))
% 43.02/43.21        | ~ (v2_funct_1 @ sk_D)
% 43.02/43.21        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 43.02/43.21        | ((sk_A) = (o_0_0_xboole_0)))),
% 43.02/43.21      inference('demod', [status(thm)], ['4', '7', '8', '9'])).
% 43.02/43.21  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('12', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 43.02/43.21      inference('cnf', [status(esa)], [d2_xboole_0])).
% 43.02/43.21  thf('13', plain, (((sk_A) != (o_0_0_xboole_0))),
% 43.02/43.21      inference('demod', [status(thm)], ['11', '12'])).
% 43.02/43.21  thf('14', plain,
% 43.02/43.21      ((((k2_relat_1 @ sk_D) != (sk_A))
% 43.02/43.21        | ~ (v2_funct_1 @ sk_D)
% 43.02/43.21        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 43.02/43.21      inference('simplify_reflect-', [status(thm)], ['10', '13'])).
% 43.02/43.21  thf('15', plain,
% 43.02/43.21      ((r2_relset_1 @ sk_A @ sk_A @ 
% 43.02/43.21        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 43.02/43.21        (k6_partfun1 @ sk_A))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('16', plain,
% 43.02/43.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('17', plain,
% 43.02/43.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf(dt_k1_partfun1, axiom,
% 43.02/43.21    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 43.02/43.21     ( ( ( v1_funct_1 @ E ) & 
% 43.02/43.21         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 43.02/43.21         ( v1_funct_1 @ F ) & 
% 43.02/43.21         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 43.02/43.21       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 43.02/43.21         ( m1_subset_1 @
% 43.02/43.21           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 43.02/43.21           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 43.02/43.21  thf('18', plain,
% 43.02/43.21      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 43.02/43.21         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 43.02/43.21          | ~ (v1_funct_1 @ X23)
% 43.02/43.21          | ~ (v1_funct_1 @ X26)
% 43.02/43.21          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 43.02/43.21          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 43.02/43.21             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 43.02/43.21      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 43.02/43.21  thf('19', plain,
% 43.02/43.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.02/43.21         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 43.02/43.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 43.02/43.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 43.02/43.21          | ~ (v1_funct_1 @ X1)
% 43.02/43.21          | ~ (v1_funct_1 @ sk_C))),
% 43.02/43.21      inference('sup-', [status(thm)], ['17', '18'])).
% 43.02/43.21  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('21', plain,
% 43.02/43.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.02/43.21         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 43.02/43.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 43.02/43.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 43.02/43.21          | ~ (v1_funct_1 @ X1))),
% 43.02/43.21      inference('demod', [status(thm)], ['19', '20'])).
% 43.02/43.21  thf('22', plain,
% 43.02/43.21      ((~ (v1_funct_1 @ sk_D)
% 43.02/43.21        | (m1_subset_1 @ 
% 43.02/43.21           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 43.02/43.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 43.02/43.21      inference('sup-', [status(thm)], ['16', '21'])).
% 43.02/43.21  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('24', plain,
% 43.02/43.21      ((m1_subset_1 @ 
% 43.02/43.21        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 43.02/43.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 43.02/43.21      inference('demod', [status(thm)], ['22', '23'])).
% 43.02/43.21  thf(redefinition_r2_relset_1, axiom,
% 43.02/43.21    (![A:$i,B:$i,C:$i,D:$i]:
% 43.02/43.21     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 43.02/43.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 43.02/43.21       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 43.02/43.21  thf('25', plain,
% 43.02/43.21      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 43.02/43.21         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 43.02/43.21          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 43.02/43.21          | ((X18) = (X21))
% 43.02/43.21          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 43.02/43.21      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 43.02/43.21  thf('26', plain,
% 43.02/43.21      (![X0 : $i]:
% 43.02/43.21         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 43.02/43.21             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 43.02/43.21          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 43.02/43.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 43.02/43.21      inference('sup-', [status(thm)], ['24', '25'])).
% 43.02/43.21  thf('27', plain,
% 43.02/43.21      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 43.02/43.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 43.02/43.21        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 43.02/43.21            = (k6_partfun1 @ sk_A)))),
% 43.02/43.21      inference('sup-', [status(thm)], ['15', '26'])).
% 43.02/43.21  thf(t29_relset_1, axiom,
% 43.02/43.21    (![A:$i]:
% 43.02/43.21     ( m1_subset_1 @
% 43.02/43.21       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 43.02/43.21  thf('28', plain,
% 43.02/43.21      (![X22 : $i]:
% 43.02/43.21         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 43.02/43.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 43.02/43.21      inference('cnf', [status(esa)], [t29_relset_1])).
% 43.02/43.21  thf(redefinition_k6_partfun1, axiom,
% 43.02/43.21    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 43.02/43.21  thf('29', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 43.02/43.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 43.02/43.21  thf('30', plain,
% 43.02/43.21      (![X22 : $i]:
% 43.02/43.21         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 43.02/43.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 43.02/43.21      inference('demod', [status(thm)], ['28', '29'])).
% 43.02/43.21  thf('31', plain,
% 43.02/43.21      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 43.02/43.21         = (k6_partfun1 @ sk_A))),
% 43.02/43.21      inference('demod', [status(thm)], ['27', '30'])).
% 43.02/43.21  thf('32', plain,
% 43.02/43.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf(t24_funct_2, axiom,
% 43.02/43.21    (![A:$i,B:$i,C:$i]:
% 43.02/43.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 43.02/43.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 43.02/43.21       ( ![D:$i]:
% 43.02/43.21         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 43.02/43.21             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 43.02/43.21           ( ( r2_relset_1 @
% 43.02/43.21               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 43.02/43.21               ( k6_partfun1 @ B ) ) =>
% 43.02/43.21             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 43.02/43.21  thf('33', plain,
% 43.02/43.21      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 43.02/43.21         (~ (v1_funct_1 @ X36)
% 43.02/43.21          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 43.02/43.21          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 43.02/43.21          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 43.02/43.21               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 43.02/43.21               (k6_partfun1 @ X37))
% 43.02/43.21          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 43.02/43.21          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 43.02/43.21          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 43.02/43.21          | ~ (v1_funct_1 @ X39))),
% 43.02/43.21      inference('cnf', [status(esa)], [t24_funct_2])).
% 43.02/43.21  thf('34', plain,
% 43.02/43.21      (![X0 : $i]:
% 43.02/43.21         (~ (v1_funct_1 @ X0)
% 43.02/43.21          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 43.02/43.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 43.02/43.21          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 43.02/43.21          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 43.02/43.21               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 43.02/43.21               (k6_partfun1 @ sk_A))
% 43.02/43.21          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 43.02/43.21          | ~ (v1_funct_1 @ sk_C))),
% 43.02/43.21      inference('sup-', [status(thm)], ['32', '33'])).
% 43.02/43.21  thf('35', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('37', plain,
% 43.02/43.21      (![X0 : $i]:
% 43.02/43.21         (~ (v1_funct_1 @ X0)
% 43.02/43.21          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 43.02/43.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 43.02/43.21          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 43.02/43.21          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 43.02/43.21               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 43.02/43.21               (k6_partfun1 @ sk_A)))),
% 43.02/43.21      inference('demod', [status(thm)], ['34', '35', '36'])).
% 43.02/43.21  thf('38', plain,
% 43.02/43.21      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 43.02/43.21           (k6_partfun1 @ sk_A))
% 43.02/43.21        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 43.02/43.21        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 43.02/43.21        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 43.02/43.21        | ~ (v1_funct_1 @ sk_D))),
% 43.02/43.21      inference('sup-', [status(thm)], ['31', '37'])).
% 43.02/43.21  thf('39', plain,
% 43.02/43.21      (![X22 : $i]:
% 43.02/43.21         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 43.02/43.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 43.02/43.21      inference('demod', [status(thm)], ['28', '29'])).
% 43.02/43.21  thf('40', plain,
% 43.02/43.21      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 43.02/43.21         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 43.02/43.21          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 43.02/43.21          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 43.02/43.21          | ((X18) != (X21)))),
% 43.02/43.21      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 43.02/43.21  thf('41', plain,
% 43.02/43.21      (![X19 : $i, X20 : $i, X21 : $i]:
% 43.02/43.21         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 43.02/43.21          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 43.02/43.21      inference('simplify', [status(thm)], ['40'])).
% 43.02/43.21  thf('42', plain,
% 43.02/43.21      (![X0 : $i]:
% 43.02/43.21         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 43.02/43.21      inference('sup-', [status(thm)], ['39', '41'])).
% 43.02/43.21  thf('43', plain,
% 43.02/43.21      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 43.02/43.21      inference('sup-', [status(thm)], ['5', '6'])).
% 43.02/43.21  thf('44', plain,
% 43.02/43.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('45', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('47', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 43.02/43.21      inference('demod', [status(thm)], ['38', '42', '43', '44', '45', '46'])).
% 43.02/43.21  thf('48', plain,
% 43.02/43.21      ((((sk_A) != (sk_A))
% 43.02/43.21        | ~ (v2_funct_1 @ sk_D)
% 43.02/43.21        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 43.02/43.21      inference('demod', [status(thm)], ['14', '47'])).
% 43.02/43.21  thf('49', plain,
% 43.02/43.21      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 43.02/43.21        | ~ (v2_funct_1 @ sk_D))),
% 43.02/43.21      inference('simplify', [status(thm)], ['48'])).
% 43.02/43.21  thf('50', plain,
% 43.02/43.21      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 43.02/43.21         = (k6_partfun1 @ sk_A))),
% 43.02/43.21      inference('demod', [status(thm)], ['27', '30'])).
% 43.02/43.21  thf('51', plain,
% 43.02/43.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf(t30_funct_2, axiom,
% 43.02/43.21    (![A:$i,B:$i,C:$i,D:$i]:
% 43.02/43.21     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 43.02/43.21         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 43.02/43.21       ( ![E:$i]:
% 43.02/43.21         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 43.02/43.21             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 43.02/43.21           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 43.02/43.21               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 43.02/43.21             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 43.02/43.21               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 43.02/43.21  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 43.02/43.21  thf(zf_stmt_2, axiom,
% 43.02/43.21    (![C:$i,B:$i]:
% 43.02/43.21     ( ( zip_tseitin_1 @ C @ B ) =>
% 43.02/43.21       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 43.02/43.21  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 43.02/43.21  thf(zf_stmt_4, axiom,
% 43.02/43.21    (![E:$i,D:$i]:
% 43.02/43.21     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 43.02/43.21  thf(zf_stmt_5, axiom,
% 43.02/43.21    (![A:$i,B:$i,C:$i,D:$i]:
% 43.02/43.21     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 43.02/43.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 43.02/43.21       ( ![E:$i]:
% 43.02/43.21         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 43.02/43.21             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 43.02/43.21           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 43.02/43.21               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 43.02/43.21             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 43.02/43.21  thf('52', plain,
% 43.02/43.21      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 43.02/43.21         (~ (v1_funct_1 @ X44)
% 43.02/43.21          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 43.02/43.21          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 43.02/43.21          | (zip_tseitin_0 @ X44 @ X47)
% 43.02/43.21          | ~ (v2_funct_1 @ (k1_partfun1 @ X48 @ X45 @ X45 @ X46 @ X47 @ X44))
% 43.02/43.21          | (zip_tseitin_1 @ X46 @ X45)
% 43.02/43.21          | ((k2_relset_1 @ X48 @ X45 @ X47) != (X45))
% 43.02/43.21          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X45)))
% 43.02/43.21          | ~ (v1_funct_2 @ X47 @ X48 @ X45)
% 43.02/43.21          | ~ (v1_funct_1 @ X47))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 43.02/43.21  thf('53', plain,
% 43.02/43.21      (![X0 : $i, X1 : $i]:
% 43.02/43.21         (~ (v1_funct_1 @ X0)
% 43.02/43.21          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 43.02/43.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 43.02/43.21          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 43.02/43.21          | (zip_tseitin_1 @ sk_A @ sk_B)
% 43.02/43.21          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 43.02/43.21          | (zip_tseitin_0 @ sk_D @ X0)
% 43.02/43.21          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 43.02/43.21          | ~ (v1_funct_1 @ sk_D))),
% 43.02/43.21      inference('sup-', [status(thm)], ['51', '52'])).
% 43.02/43.21  thf('54', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('56', plain,
% 43.02/43.21      (![X0 : $i, X1 : $i]:
% 43.02/43.21         (~ (v1_funct_1 @ X0)
% 43.02/43.21          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 43.02/43.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 43.02/43.21          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 43.02/43.21          | (zip_tseitin_1 @ sk_A @ sk_B)
% 43.02/43.21          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 43.02/43.21          | (zip_tseitin_0 @ sk_D @ X0))),
% 43.02/43.21      inference('demod', [status(thm)], ['53', '54', '55'])).
% 43.02/43.21  thf('57', plain,
% 43.02/43.21      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 43.02/43.21        | (zip_tseitin_0 @ sk_D @ sk_C)
% 43.02/43.21        | (zip_tseitin_1 @ sk_A @ sk_B)
% 43.02/43.21        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 43.02/43.21        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 43.02/43.21        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 43.02/43.21        | ~ (v1_funct_1 @ sk_C))),
% 43.02/43.21      inference('sup-', [status(thm)], ['50', '56'])).
% 43.02/43.21  thf(fc4_funct_1, axiom,
% 43.02/43.21    (![A:$i]:
% 43.02/43.21     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 43.02/43.21       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 43.02/43.21  thf('58', plain, (![X9 : $i]: (v2_funct_1 @ (k6_relat_1 @ X9))),
% 43.02/43.21      inference('cnf', [status(esa)], [fc4_funct_1])).
% 43.02/43.21  thf('59', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 43.02/43.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 43.02/43.21  thf('60', plain, (![X9 : $i]: (v2_funct_1 @ (k6_partfun1 @ X9))),
% 43.02/43.21      inference('demod', [status(thm)], ['58', '59'])).
% 43.02/43.21  thf('61', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('62', plain,
% 43.02/43.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('63', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('65', plain,
% 43.02/43.21      (((zip_tseitin_0 @ sk_D @ sk_C)
% 43.02/43.21        | (zip_tseitin_1 @ sk_A @ sk_B)
% 43.02/43.21        | ((sk_B) != (sk_B)))),
% 43.02/43.21      inference('demod', [status(thm)], ['57', '60', '61', '62', '63', '64'])).
% 43.02/43.21  thf('66', plain,
% 43.02/43.21      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 43.02/43.21      inference('simplify', [status(thm)], ['65'])).
% 43.02/43.21  thf('67', plain,
% 43.02/43.21      (![X42 : $i, X43 : $i]:
% 43.02/43.21         (((X42) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X42 @ X43))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_2])).
% 43.02/43.21  thf('68', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 43.02/43.21      inference('cnf', [status(esa)], [d2_xboole_0])).
% 43.02/43.21  thf('69', plain,
% 43.02/43.21      (![X42 : $i, X43 : $i]:
% 43.02/43.21         (((X42) = (o_0_0_xboole_0)) | ~ (zip_tseitin_1 @ X42 @ X43))),
% 43.02/43.21      inference('demod', [status(thm)], ['67', '68'])).
% 43.02/43.21  thf('70', plain,
% 43.02/43.21      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (o_0_0_xboole_0)))),
% 43.02/43.21      inference('sup-', [status(thm)], ['66', '69'])).
% 43.02/43.21  thf('71', plain, (((sk_A) != (o_0_0_xboole_0))),
% 43.02/43.21      inference('demod', [status(thm)], ['11', '12'])).
% 43.02/43.21  thf('72', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 43.02/43.21      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 43.02/43.21  thf('73', plain,
% 43.02/43.21      (![X40 : $i, X41 : $i]:
% 43.02/43.21         ((v2_funct_1 @ X41) | ~ (zip_tseitin_0 @ X41 @ X40))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_4])).
% 43.02/43.21  thf('74', plain, ((v2_funct_1 @ sk_D)),
% 43.02/43.21      inference('sup-', [status(thm)], ['72', '73'])).
% 43.02/43.21  thf('75', plain,
% 43.02/43.21      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 43.02/43.21      inference('demod', [status(thm)], ['49', '74'])).
% 43.02/43.21  thf(t58_funct_1, axiom,
% 43.02/43.21    (![A:$i]:
% 43.02/43.21     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 43.02/43.21       ( ( v2_funct_1 @ A ) =>
% 43.02/43.21         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 43.02/43.21             ( k1_relat_1 @ A ) ) & 
% 43.02/43.21           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 43.02/43.21             ( k1_relat_1 @ A ) ) ) ) ))).
% 43.02/43.21  thf('76', plain,
% 43.02/43.21      (![X11 : $i]:
% 43.02/43.21         (~ (v2_funct_1 @ X11)
% 43.02/43.21          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ (k2_funct_1 @ X11)))
% 43.02/43.21              = (k1_relat_1 @ X11))
% 43.02/43.21          | ~ (v1_funct_1 @ X11)
% 43.02/43.21          | ~ (v1_relat_1 @ X11))),
% 43.02/43.21      inference('cnf', [status(esa)], [t58_funct_1])).
% 43.02/43.21  thf('77', plain,
% 43.02/43.21      ((((k2_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 43.02/43.21        | ~ (v1_relat_1 @ sk_D)
% 43.02/43.21        | ~ (v1_funct_1 @ sk_D)
% 43.02/43.21        | ~ (v2_funct_1 @ sk_D))),
% 43.02/43.21      inference('sup+', [status(thm)], ['75', '76'])).
% 43.02/43.21  thf(t71_relat_1, axiom,
% 43.02/43.21    (![A:$i]:
% 43.02/43.21     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 43.02/43.21       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 43.02/43.21  thf('78', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 43.02/43.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 43.02/43.21  thf('79', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 43.02/43.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 43.02/43.21  thf('80', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 43.02/43.21      inference('demod', [status(thm)], ['78', '79'])).
% 43.02/43.21  thf('81', plain,
% 43.02/43.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf(cc1_relset_1, axiom,
% 43.02/43.21    (![A:$i,B:$i,C:$i]:
% 43.02/43.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 43.02/43.21       ( v1_relat_1 @ C ) ))).
% 43.02/43.21  thf('82', plain,
% 43.02/43.21      (![X12 : $i, X13 : $i, X14 : $i]:
% 43.02/43.21         ((v1_relat_1 @ X12)
% 43.02/43.21          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 43.02/43.21      inference('cnf', [status(esa)], [cc1_relset_1])).
% 43.02/43.21  thf('83', plain, ((v1_relat_1 @ sk_D)),
% 43.02/43.21      inference('sup-', [status(thm)], ['81', '82'])).
% 43.02/43.21  thf('84', plain, ((v1_funct_1 @ sk_D)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('85', plain, ((v2_funct_1 @ sk_D)),
% 43.02/43.21      inference('sup-', [status(thm)], ['72', '73'])).
% 43.02/43.21  thf('86', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 43.02/43.21      inference('demod', [status(thm)], ['77', '80', '83', '84', '85'])).
% 43.02/43.21  thf(t78_relat_1, axiom,
% 43.02/43.21    (![A:$i]:
% 43.02/43.21     ( ( v1_relat_1 @ A ) =>
% 43.02/43.21       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 43.02/43.21  thf('87', plain,
% 43.02/43.21      (![X5 : $i]:
% 43.02/43.21         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 43.02/43.21          | ~ (v1_relat_1 @ X5))),
% 43.02/43.21      inference('cnf', [status(esa)], [t78_relat_1])).
% 43.02/43.21  thf('88', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 43.02/43.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 43.02/43.21  thf('89', plain,
% 43.02/43.21      (![X5 : $i]:
% 43.02/43.21         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 43.02/43.21          | ~ (v1_relat_1 @ X5))),
% 43.02/43.21      inference('demod', [status(thm)], ['87', '88'])).
% 43.02/43.21  thf('90', plain,
% 43.02/43.21      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 43.02/43.21        | ~ (v1_relat_1 @ sk_D))),
% 43.02/43.21      inference('sup+', [status(thm)], ['86', '89'])).
% 43.02/43.21  thf('91', plain,
% 43.02/43.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('92', plain,
% 43.02/43.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf(redefinition_k1_partfun1, axiom,
% 43.02/43.21    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 43.02/43.21     ( ( ( v1_funct_1 @ E ) & 
% 43.02/43.21         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 43.02/43.21         ( v1_funct_1 @ F ) & 
% 43.02/43.21         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 43.02/43.21       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 43.02/43.21  thf('93', plain,
% 43.02/43.21      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 43.02/43.21         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 43.02/43.21          | ~ (v1_funct_1 @ X29)
% 43.02/43.21          | ~ (v1_funct_1 @ X32)
% 43.02/43.21          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 43.02/43.21          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 43.02/43.21              = (k5_relat_1 @ X29 @ X32)))),
% 43.02/43.21      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 43.02/43.21  thf('94', plain,
% 43.02/43.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.02/43.21         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 43.02/43.21            = (k5_relat_1 @ sk_C @ X0))
% 43.02/43.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 43.02/43.21          | ~ (v1_funct_1 @ X0)
% 43.02/43.21          | ~ (v1_funct_1 @ sk_C))),
% 43.02/43.21      inference('sup-', [status(thm)], ['92', '93'])).
% 43.02/43.21  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('96', plain,
% 43.02/43.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.02/43.21         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 43.02/43.21            = (k5_relat_1 @ sk_C @ X0))
% 43.02/43.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 43.02/43.21          | ~ (v1_funct_1 @ X0))),
% 43.02/43.21      inference('demod', [status(thm)], ['94', '95'])).
% 43.02/43.21  thf('97', plain,
% 43.02/43.21      ((~ (v1_funct_1 @ sk_D)
% 43.02/43.21        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 43.02/43.21            = (k5_relat_1 @ sk_C @ sk_D)))),
% 43.02/43.21      inference('sup-', [status(thm)], ['91', '96'])).
% 43.02/43.21  thf('98', plain, ((v1_funct_1 @ sk_D)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('99', plain,
% 43.02/43.21      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 43.02/43.21         = (k6_partfun1 @ sk_A))),
% 43.02/43.21      inference('demod', [status(thm)], ['27', '30'])).
% 43.02/43.21  thf('100', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 43.02/43.21      inference('demod', [status(thm)], ['97', '98', '99'])).
% 43.02/43.21  thf(dt_k2_funct_1, axiom,
% 43.02/43.21    (![A:$i]:
% 43.02/43.21     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 43.02/43.21       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 43.02/43.21         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 43.02/43.21  thf('101', plain,
% 43.02/43.21      (![X7 : $i]:
% 43.02/43.21         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 43.02/43.21          | ~ (v1_funct_1 @ X7)
% 43.02/43.21          | ~ (v1_relat_1 @ X7))),
% 43.02/43.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 43.02/43.21  thf('102', plain,
% 43.02/43.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('103', plain,
% 43.02/43.21      (![X49 : $i, X50 : $i, X51 : $i]:
% 43.02/43.21         (((X49) = (k1_xboole_0))
% 43.02/43.21          | ~ (v1_funct_1 @ X50)
% 43.02/43.21          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 43.02/43.21          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 43.02/43.21          | ((k5_relat_1 @ (k2_funct_1 @ X50) @ X50) = (k6_partfun1 @ X49))
% 43.02/43.21          | ~ (v2_funct_1 @ X50)
% 43.02/43.21          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 43.02/43.21      inference('cnf', [status(esa)], [t35_funct_2])).
% 43.02/43.21  thf('104', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 43.02/43.21      inference('cnf', [status(esa)], [d2_xboole_0])).
% 43.02/43.21  thf('105', plain,
% 43.02/43.21      (![X49 : $i, X50 : $i, X51 : $i]:
% 43.02/43.21         (((X49) = (o_0_0_xboole_0))
% 43.02/43.21          | ~ (v1_funct_1 @ X50)
% 43.02/43.21          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 43.02/43.21          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 43.02/43.21          | ((k5_relat_1 @ (k2_funct_1 @ X50) @ X50) = (k6_partfun1 @ X49))
% 43.02/43.21          | ~ (v2_funct_1 @ X50)
% 43.02/43.21          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 43.02/43.21      inference('demod', [status(thm)], ['103', '104'])).
% 43.02/43.21  thf('106', plain,
% 43.02/43.21      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 43.02/43.21        | ~ (v2_funct_1 @ sk_C)
% 43.02/43.21        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 43.02/43.21        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 43.02/43.21        | ~ (v1_funct_1 @ sk_C)
% 43.02/43.21        | ((sk_B) = (o_0_0_xboole_0)))),
% 43.02/43.21      inference('sup-', [status(thm)], ['102', '105'])).
% 43.02/43.21  thf('107', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('109', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('111', plain,
% 43.02/43.21      ((((sk_B) != (sk_B))
% 43.02/43.21        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 43.02/43.21        | ((sk_B) = (o_0_0_xboole_0)))),
% 43.02/43.21      inference('demod', [status(thm)], ['106', '107', '108', '109', '110'])).
% 43.02/43.21  thf('112', plain,
% 43.02/43.21      ((((sk_B) = (o_0_0_xboole_0))
% 43.02/43.21        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 43.02/43.21      inference('simplify', [status(thm)], ['111'])).
% 43.02/43.21  thf('113', plain, (((sk_B) != (k1_xboole_0))),
% 43.02/43.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.21  thf('114', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 43.02/43.21      inference('cnf', [status(esa)], [d2_xboole_0])).
% 43.02/43.21  thf('115', plain, (((sk_B) != (o_0_0_xboole_0))),
% 43.02/43.21      inference('demod', [status(thm)], ['113', '114'])).
% 43.02/43.21  thf('116', plain,
% 43.02/43.21      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 43.02/43.21      inference('simplify_reflect-', [status(thm)], ['112', '115'])).
% 43.02/43.21  thf(t55_relat_1, axiom,
% 43.02/43.21    (![A:$i]:
% 43.02/43.21     ( ( v1_relat_1 @ A ) =>
% 43.02/43.21       ( ![B:$i]:
% 43.02/43.21         ( ( v1_relat_1 @ B ) =>
% 43.02/43.21           ( ![C:$i]:
% 43.02/43.21             ( ( v1_relat_1 @ C ) =>
% 43.02/43.21               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 43.02/43.21                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 43.02/43.21  thf('117', plain,
% 43.02/43.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.02/43.21         (~ (v1_relat_1 @ X0)
% 43.02/43.21          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 43.02/43.21              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 43.02/43.21          | ~ (v1_relat_1 @ X2)
% 43.02/43.21          | ~ (v1_relat_1 @ X1))),
% 43.02/43.21      inference('cnf', [status(esa)], [t55_relat_1])).
% 43.02/43.21  thf('118', plain,
% 43.02/43.21      (![X0 : $i]:
% 43.02/43.21         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 43.02/43.21            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 43.02/43.21          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 43.02/43.21          | ~ (v1_relat_1 @ X0)
% 43.02/43.21          | ~ (v1_relat_1 @ sk_C))),
% 43.02/43.21      inference('sup+', [status(thm)], ['116', '117'])).
% 43.02/43.21  thf('119', plain,
% 43.02/43.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('120', plain,
% 43.02/43.22      (![X12 : $i, X13 : $i, X14 : $i]:
% 43.02/43.22         ((v1_relat_1 @ X12)
% 43.02/43.22          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 43.02/43.22      inference('cnf', [status(esa)], [cc1_relset_1])).
% 43.02/43.22  thf('121', plain, ((v1_relat_1 @ sk_C)),
% 43.02/43.22      inference('sup-', [status(thm)], ['119', '120'])).
% 43.02/43.22  thf('122', plain,
% 43.02/43.22      (![X0 : $i]:
% 43.02/43.22         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 43.02/43.22            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 43.02/43.22          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 43.02/43.22          | ~ (v1_relat_1 @ X0))),
% 43.02/43.22      inference('demod', [status(thm)], ['118', '121'])).
% 43.02/43.22  thf('123', plain,
% 43.02/43.22      (![X0 : $i]:
% 43.02/43.22         (~ (v1_relat_1 @ sk_C)
% 43.02/43.22          | ~ (v1_funct_1 @ sk_C)
% 43.02/43.22          | ~ (v1_relat_1 @ X0)
% 43.02/43.22          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 43.02/43.22              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 43.02/43.22      inference('sup-', [status(thm)], ['101', '122'])).
% 43.02/43.22  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 43.02/43.22      inference('sup-', [status(thm)], ['119', '120'])).
% 43.02/43.22  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('126', plain,
% 43.02/43.22      (![X0 : $i]:
% 43.02/43.22         (~ (v1_relat_1 @ X0)
% 43.02/43.22          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 43.02/43.22              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 43.02/43.22      inference('demod', [status(thm)], ['123', '124', '125'])).
% 43.02/43.22  thf('127', plain,
% 43.02/43.22      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 43.02/43.22          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 43.02/43.22        | ~ (v1_relat_1 @ sk_D))),
% 43.02/43.22      inference('sup+', [status(thm)], ['100', '126'])).
% 43.02/43.22  thf('128', plain,
% 43.02/43.22      (![X7 : $i]:
% 43.02/43.22         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 43.02/43.22          | ~ (v1_funct_1 @ X7)
% 43.02/43.22          | ~ (v1_relat_1 @ X7))),
% 43.02/43.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 43.02/43.22  thf(t55_funct_1, axiom,
% 43.02/43.22    (![A:$i]:
% 43.02/43.22     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 43.02/43.22       ( ( v2_funct_1 @ A ) =>
% 43.02/43.22         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 43.02/43.22           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 43.02/43.22  thf('129', plain,
% 43.02/43.22      (![X10 : $i]:
% 43.02/43.22         (~ (v2_funct_1 @ X10)
% 43.02/43.22          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 43.02/43.22          | ~ (v1_funct_1 @ X10)
% 43.02/43.22          | ~ (v1_relat_1 @ X10))),
% 43.02/43.22      inference('cnf', [status(esa)], [t55_funct_1])).
% 43.02/43.22  thf(t80_relat_1, axiom,
% 43.02/43.22    (![A:$i]:
% 43.02/43.22     ( ( v1_relat_1 @ A ) =>
% 43.02/43.22       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 43.02/43.22  thf('130', plain,
% 43.02/43.22      (![X6 : $i]:
% 43.02/43.22         (((k5_relat_1 @ X6 @ (k6_relat_1 @ (k2_relat_1 @ X6))) = (X6))
% 43.02/43.22          | ~ (v1_relat_1 @ X6))),
% 43.02/43.22      inference('cnf', [status(esa)], [t80_relat_1])).
% 43.02/43.22  thf('131', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 43.02/43.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 43.02/43.22  thf('132', plain,
% 43.02/43.22      (![X6 : $i]:
% 43.02/43.22         (((k5_relat_1 @ X6 @ (k6_partfun1 @ (k2_relat_1 @ X6))) = (X6))
% 43.02/43.22          | ~ (v1_relat_1 @ X6))),
% 43.02/43.22      inference('demod', [status(thm)], ['130', '131'])).
% 43.02/43.22  thf('133', plain,
% 43.02/43.22      (![X0 : $i]:
% 43.02/43.22         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 43.02/43.22            = (k2_funct_1 @ X0))
% 43.02/43.22          | ~ (v1_relat_1 @ X0)
% 43.02/43.22          | ~ (v1_funct_1 @ X0)
% 43.02/43.22          | ~ (v2_funct_1 @ X0)
% 43.02/43.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 43.02/43.22      inference('sup+', [status(thm)], ['129', '132'])).
% 43.02/43.22  thf('134', plain,
% 43.02/43.22      (![X0 : $i]:
% 43.02/43.22         (~ (v1_relat_1 @ X0)
% 43.02/43.22          | ~ (v1_funct_1 @ X0)
% 43.02/43.22          | ~ (v2_funct_1 @ X0)
% 43.02/43.22          | ~ (v1_funct_1 @ X0)
% 43.02/43.22          | ~ (v1_relat_1 @ X0)
% 43.02/43.22          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 43.02/43.22              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 43.02/43.22      inference('sup-', [status(thm)], ['128', '133'])).
% 43.02/43.22  thf('135', plain,
% 43.02/43.22      (![X0 : $i]:
% 43.02/43.22         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 43.02/43.22            = (k2_funct_1 @ X0))
% 43.02/43.22          | ~ (v2_funct_1 @ X0)
% 43.02/43.22          | ~ (v1_funct_1 @ X0)
% 43.02/43.22          | ~ (v1_relat_1 @ X0))),
% 43.02/43.22      inference('simplify', [status(thm)], ['134'])).
% 43.02/43.22  thf('136', plain,
% 43.02/43.22      (![X7 : $i]:
% 43.02/43.22         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 43.02/43.22          | ~ (v1_funct_1 @ X7)
% 43.02/43.22          | ~ (v1_relat_1 @ X7))),
% 43.02/43.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 43.02/43.22  thf('137', plain,
% 43.02/43.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('138', plain,
% 43.02/43.22      (![X15 : $i, X16 : $i, X17 : $i]:
% 43.02/43.22         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 43.02/43.22          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 43.02/43.22      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 43.02/43.22  thf('139', plain,
% 43.02/43.22      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 43.02/43.22      inference('sup-', [status(thm)], ['137', '138'])).
% 43.02/43.22  thf('140', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('141', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 43.02/43.22      inference('sup+', [status(thm)], ['139', '140'])).
% 43.02/43.22  thf('142', plain,
% 43.02/43.22      (![X7 : $i]:
% 43.02/43.22         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 43.02/43.22          | ~ (v1_funct_1 @ X7)
% 43.02/43.22          | ~ (v1_relat_1 @ X7))),
% 43.02/43.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 43.02/43.22  thf('143', plain,
% 43.02/43.22      (![X10 : $i]:
% 43.02/43.22         (~ (v2_funct_1 @ X10)
% 43.02/43.22          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 43.02/43.22          | ~ (v1_funct_1 @ X10)
% 43.02/43.22          | ~ (v1_relat_1 @ X10))),
% 43.02/43.22      inference('cnf', [status(esa)], [t55_funct_1])).
% 43.02/43.22  thf('144', plain,
% 43.02/43.22      (![X5 : $i]:
% 43.02/43.22         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 43.02/43.22          | ~ (v1_relat_1 @ X5))),
% 43.02/43.22      inference('demod', [status(thm)], ['87', '88'])).
% 43.02/43.22  thf('145', plain,
% 43.02/43.22      (![X0 : $i]:
% 43.02/43.22         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 43.02/43.22            = (k2_funct_1 @ X0))
% 43.02/43.22          | ~ (v1_relat_1 @ X0)
% 43.02/43.22          | ~ (v1_funct_1 @ X0)
% 43.02/43.22          | ~ (v2_funct_1 @ X0)
% 43.02/43.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 43.02/43.22      inference('sup+', [status(thm)], ['143', '144'])).
% 43.02/43.22  thf('146', plain,
% 43.02/43.22      (![X0 : $i]:
% 43.02/43.22         (~ (v1_relat_1 @ X0)
% 43.02/43.22          | ~ (v1_funct_1 @ X0)
% 43.02/43.22          | ~ (v2_funct_1 @ X0)
% 43.02/43.22          | ~ (v1_funct_1 @ X0)
% 43.02/43.22          | ~ (v1_relat_1 @ X0)
% 43.02/43.22          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 43.02/43.22              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 43.02/43.22      inference('sup-', [status(thm)], ['142', '145'])).
% 43.02/43.22  thf('147', plain,
% 43.02/43.22      (![X0 : $i]:
% 43.02/43.22         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 43.02/43.22            = (k2_funct_1 @ X0))
% 43.02/43.22          | ~ (v2_funct_1 @ X0)
% 43.02/43.22          | ~ (v1_funct_1 @ X0)
% 43.02/43.22          | ~ (v1_relat_1 @ X0))),
% 43.02/43.22      inference('simplify', [status(thm)], ['146'])).
% 43.02/43.22  thf('148', plain,
% 43.02/43.22      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 43.02/43.22          = (k2_funct_1 @ sk_C))
% 43.02/43.22        | ~ (v1_relat_1 @ sk_C)
% 43.02/43.22        | ~ (v1_funct_1 @ sk_C)
% 43.02/43.22        | ~ (v2_funct_1 @ sk_C))),
% 43.02/43.22      inference('sup+', [status(thm)], ['141', '147'])).
% 43.02/43.22  thf('149', plain, ((v1_relat_1 @ sk_C)),
% 43.02/43.22      inference('sup-', [status(thm)], ['119', '120'])).
% 43.02/43.22  thf('150', plain, ((v1_funct_1 @ sk_C)),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('151', plain, ((v2_funct_1 @ sk_C)),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('152', plain,
% 43.02/43.22      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 43.02/43.22         = (k2_funct_1 @ sk_C))),
% 43.02/43.22      inference('demod', [status(thm)], ['148', '149', '150', '151'])).
% 43.02/43.22  thf('153', plain,
% 43.02/43.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.02/43.22         (~ (v1_relat_1 @ X0)
% 43.02/43.22          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 43.02/43.22              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 43.02/43.22          | ~ (v1_relat_1 @ X2)
% 43.02/43.22          | ~ (v1_relat_1 @ X1))),
% 43.02/43.22      inference('cnf', [status(esa)], [t55_relat_1])).
% 43.02/43.22  thf('154', plain,
% 43.02/43.22      (![X0 : $i]:
% 43.02/43.22         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 43.02/43.22            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 43.02/43.22               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 43.02/43.22          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 43.02/43.22          | ~ (v1_relat_1 @ X0)
% 43.02/43.22          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 43.02/43.22      inference('sup+', [status(thm)], ['152', '153'])).
% 43.02/43.22  thf('155', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 43.02/43.22      inference('cnf', [status(esa)], [fc4_funct_1])).
% 43.02/43.22  thf('156', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 43.02/43.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 43.02/43.22  thf('157', plain, (![X8 : $i]: (v1_relat_1 @ (k6_partfun1 @ X8))),
% 43.02/43.22      inference('demod', [status(thm)], ['155', '156'])).
% 43.02/43.22  thf('158', plain,
% 43.02/43.22      (![X0 : $i]:
% 43.02/43.22         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 43.02/43.22            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 43.02/43.22               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 43.02/43.22          | ~ (v1_relat_1 @ X0)
% 43.02/43.22          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 43.02/43.22      inference('demod', [status(thm)], ['154', '157'])).
% 43.02/43.22  thf('159', plain,
% 43.02/43.22      (![X0 : $i]:
% 43.02/43.22         (~ (v1_relat_1 @ sk_C)
% 43.02/43.22          | ~ (v1_funct_1 @ sk_C)
% 43.02/43.22          | ~ (v1_relat_1 @ X0)
% 43.02/43.22          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 43.02/43.22              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 43.02/43.22                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 43.02/43.22      inference('sup-', [status(thm)], ['136', '158'])).
% 43.02/43.22  thf('160', plain, ((v1_relat_1 @ sk_C)),
% 43.02/43.22      inference('sup-', [status(thm)], ['119', '120'])).
% 43.02/43.22  thf('161', plain, ((v1_funct_1 @ sk_C)),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('162', plain,
% 43.02/43.22      (![X0 : $i]:
% 43.02/43.22         (~ (v1_relat_1 @ X0)
% 43.02/43.22          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 43.02/43.22              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 43.02/43.22                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 43.02/43.22      inference('demod', [status(thm)], ['159', '160', '161'])).
% 43.02/43.22  thf('163', plain,
% 43.02/43.22      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 43.02/43.22          (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 43.02/43.22          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 43.02/43.22        | ~ (v1_relat_1 @ sk_C)
% 43.02/43.22        | ~ (v1_funct_1 @ sk_C)
% 43.02/43.22        | ~ (v2_funct_1 @ sk_C)
% 43.02/43.22        | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 43.02/43.22      inference('sup+', [status(thm)], ['135', '162'])).
% 43.02/43.22  thf('164', plain,
% 43.02/43.22      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 43.02/43.22         = (k2_funct_1 @ sk_C))),
% 43.02/43.22      inference('demod', [status(thm)], ['148', '149', '150', '151'])).
% 43.02/43.22  thf('165', plain, ((v1_relat_1 @ sk_C)),
% 43.02/43.22      inference('sup-', [status(thm)], ['119', '120'])).
% 43.02/43.22  thf('166', plain, ((v1_funct_1 @ sk_C)),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('167', plain, ((v2_funct_1 @ sk_C)),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('168', plain, (![X8 : $i]: (v1_relat_1 @ (k6_partfun1 @ X8))),
% 43.02/43.22      inference('demod', [status(thm)], ['155', '156'])).
% 43.02/43.22  thf('169', plain,
% 43.02/43.22      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 43.02/43.22         = (k2_funct_1 @ sk_C))),
% 43.02/43.22      inference('demod', [status(thm)],
% 43.02/43.22                ['163', '164', '165', '166', '167', '168'])).
% 43.02/43.22  thf('170', plain,
% 43.02/43.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('171', plain,
% 43.02/43.22      (![X49 : $i, X50 : $i, X51 : $i]:
% 43.02/43.22         (((X49) = (o_0_0_xboole_0))
% 43.02/43.22          | ~ (v1_funct_1 @ X50)
% 43.02/43.22          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 43.02/43.22          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 43.02/43.22          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_partfun1 @ X51))
% 43.02/43.22          | ~ (v2_funct_1 @ X50)
% 43.02/43.22          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 43.02/43.22      inference('demod', [status(thm)], ['1', '2'])).
% 43.02/43.22  thf('172', plain,
% 43.02/43.22      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 43.02/43.22        | ~ (v2_funct_1 @ sk_C)
% 43.02/43.22        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 43.02/43.22        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 43.02/43.22        | ~ (v1_funct_1 @ sk_C)
% 43.02/43.22        | ((sk_B) = (o_0_0_xboole_0)))),
% 43.02/43.22      inference('sup-', [status(thm)], ['170', '171'])).
% 43.02/43.22  thf('173', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('174', plain, ((v2_funct_1 @ sk_C)),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('175', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('177', plain,
% 43.02/43.22      ((((sk_B) != (sk_B))
% 43.02/43.22        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 43.02/43.22        | ((sk_B) = (o_0_0_xboole_0)))),
% 43.02/43.22      inference('demod', [status(thm)], ['172', '173', '174', '175', '176'])).
% 43.02/43.22  thf('178', plain,
% 43.02/43.22      ((((sk_B) = (o_0_0_xboole_0))
% 43.02/43.22        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 43.02/43.22      inference('simplify', [status(thm)], ['177'])).
% 43.02/43.22  thf('179', plain, (((sk_B) != (o_0_0_xboole_0))),
% 43.02/43.22      inference('demod', [status(thm)], ['113', '114'])).
% 43.02/43.22  thf('180', plain,
% 43.02/43.22      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 43.02/43.22      inference('simplify_reflect-', [status(thm)], ['178', '179'])).
% 43.02/43.22  thf('181', plain,
% 43.02/43.22      (![X11 : $i]:
% 43.02/43.22         (~ (v2_funct_1 @ X11)
% 43.02/43.22          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ (k2_funct_1 @ X11)))
% 43.02/43.22              = (k1_relat_1 @ X11))
% 43.02/43.22          | ~ (v1_funct_1 @ X11)
% 43.02/43.22          | ~ (v1_relat_1 @ X11))),
% 43.02/43.22      inference('cnf', [status(esa)], [t58_funct_1])).
% 43.02/43.22  thf('182', plain,
% 43.02/43.22      ((((k2_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))
% 43.02/43.22        | ~ (v1_relat_1 @ sk_C)
% 43.02/43.22        | ~ (v1_funct_1 @ sk_C)
% 43.02/43.22        | ~ (v2_funct_1 @ sk_C))),
% 43.02/43.22      inference('sup+', [status(thm)], ['180', '181'])).
% 43.02/43.22  thf('183', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 43.02/43.22      inference('demod', [status(thm)], ['78', '79'])).
% 43.02/43.22  thf('184', plain, ((v1_relat_1 @ sk_C)),
% 43.02/43.22      inference('sup-', [status(thm)], ['119', '120'])).
% 43.02/43.22  thf('185', plain, ((v1_funct_1 @ sk_C)),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('186', plain, ((v2_funct_1 @ sk_C)),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('187', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 43.02/43.22      inference('demod', [status(thm)], ['182', '183', '184', '185', '186'])).
% 43.02/43.22  thf('188', plain,
% 43.02/43.22      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 43.02/43.22         = (k2_funct_1 @ sk_C))),
% 43.02/43.22      inference('demod', [status(thm)], ['169', '187'])).
% 43.02/43.22  thf('189', plain, ((v1_relat_1 @ sk_D)),
% 43.02/43.22      inference('sup-', [status(thm)], ['81', '82'])).
% 43.02/43.22  thf('190', plain,
% 43.02/43.22      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 43.02/43.22      inference('demod', [status(thm)], ['127', '188', '189'])).
% 43.02/43.22  thf('191', plain, ((v1_relat_1 @ sk_D)),
% 43.02/43.22      inference('sup-', [status(thm)], ['81', '82'])).
% 43.02/43.22  thf('192', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 43.02/43.22      inference('demod', [status(thm)], ['90', '190', '191'])).
% 43.02/43.22  thf('193', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 43.02/43.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.02/43.22  thf('194', plain, ($false),
% 43.02/43.22      inference('simplify_reflect-', [status(thm)], ['192', '193'])).
% 43.02/43.22  
% 43.02/43.22  % SZS output end Refutation
% 43.02/43.22  
% 43.02/43.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
