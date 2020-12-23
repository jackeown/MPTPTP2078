%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DzXip8fkru

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:26 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :  254 (5494 expanded)
%              Number of leaves         :   46 (1592 expanded)
%              Depth                    :   29
%              Number of atoms          : 2713 (149302 expanded)
%              Number of equality atoms :  219 (9930 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 )
        = ( k5_relat_1 @ X31 @ X34 ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 ) ) ),
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
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X14
        = ( k2_funct_1 @ X15 ) )
      | ( ( k5_relat_1 @ X14 @ X15 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X15 ) ) )
      | ( ( k2_relat_1 @ X14 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('31',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','36','37','42','43','48'])).

thf('50',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('51',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('52',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( r2_relset_1 @ X39 @ X39 @ ( k1_partfun1 @ X39 @ X40 @ X40 @ X39 @ X38 @ X41 ) @ ( k6_partfun1 @ X39 ) )
      | ( ( k2_relset_1 @ X40 @ X39 @ X41 )
        = X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('55',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( r2_relset_1 @ X39 @ X39 @ ( k1_partfun1 @ X39 @ X40 @ X40 @ X39 @ X38 @ X41 ) @ ( k6_relat_1 @ X39 ) )
      | ( ( k2_relset_1 @ X40 @ X39 @ X41 )
        = X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('63',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 )
      | ( X19 != X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('64',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('68',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['61','65','68','69','70','71'])).

thf('73',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['49','72'])).

thf('74',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('76',plain,(
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

thf('77',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( zip_tseitin_0 @ X46 @ X49 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X50 @ X47 @ X47 @ X48 @ X49 @ X46 ) )
      | ( zip_tseitin_1 @ X48 @ X47 )
      | ( ( k2_relset_1 @ X50 @ X47 @ X49 )
       != X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X47 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('78',plain,(
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
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','81'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('83',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('84',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['82','83','84','85','86','87'])).

thf('89',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('91',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v2_funct_1 @ X43 )
      | ~ ( zip_tseitin_0 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('95',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['74','95'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('97',plain,(
    ! [X54: $i] :
      ( ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X54 ) @ ( k2_relat_1 @ X54 ) ) ) )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('98',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X54: $i] :
      ( ( v1_funct_2 @ X54 @ ( k1_relat_1 @ X54 ) @ ( k2_relat_1 @ X54 ) )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('101',plain,(
    ! [X54: $i] :
      ( ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X54 ) @ ( k2_relat_1 @ X54 ) ) ) )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

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

thf('102',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ( ( k5_relat_1 @ X52 @ ( k2_funct_1 @ X52 ) )
        = ( k6_partfun1 @ X53 ) )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X53 @ X51 @ X52 )
       != X51 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('103',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('104',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ( ( k5_relat_1 @ X52 @ ( k2_funct_1 @ X52 ) )
        = ( k6_relat_1 @ X53 ) )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X53 @ X51 @ X52 )
       != X51 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['100','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ( ( k5_relat_1 @ X52 @ ( k2_funct_1 @ X52 ) )
        = ( k6_relat_1 @ X53 ) )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X53 @ X51 @ X52 )
       != X51 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('113',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('115',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('118',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['61','65','68','69','70','71'])).

thf('121',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['93','94'])).

thf('124',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['110','124'])).

thf('126',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('128',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['93','94'])).

thf('129',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['61','65','68','69','70','71'])).

thf('130',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['125','126','127','128','129'])).

thf('131',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['130','131'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('133',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('134',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('136',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['96','136'])).

thf('138',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['137'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('139',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('141',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X14
        = ( k2_funct_1 @ X15 ) )
      | ( ( k5_relat_1 @ X14 @ X15 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X15 ) ) )
      | ( ( k2_relat_1 @ X14 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['139','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['138','145'])).

thf('147',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('149',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['93','94'])).

thf('151',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['61','65','68','69','70','71'])).

thf('152',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['137'])).

thf('153',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('154',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['137'])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['61','65','68','69','70','71'])).

thf('157',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['137'])).

thf('158',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('159',plain,(
    ! [X54: $i] :
      ( ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X54 ) @ ( k2_relat_1 @ X54 ) ) ) )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('160',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ( ( k5_relat_1 @ X52 @ ( k2_funct_1 @ X52 ) )
        = ( k6_relat_1 @ X53 ) )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X53 @ X51 @ X52 )
       != X51 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('165',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('168',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('172',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('173',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('175',plain,(
    ! [X54: $i] :
      ( ( v1_funct_2 @ X54 @ ( k1_relat_1 @ X54 ) @ ( k2_relat_1 @ X54 ) )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('176',plain,
    ( ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('178',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['165','172','173','179','180'])).

thf('182',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['182','183'])).

thf('185',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ( ( k5_relat_1 @ X52 @ ( k2_funct_1 @ X52 ) )
        = ( k6_relat_1 @ X53 ) )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X53 @ X51 @ X52 )
       != X51 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('187',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['187','188','189','190','191'])).

thf('193',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['193','194'])).

thf('196',plain,
    ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['184','195'])).

thf('197',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('198',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('200',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['137'])).

thf('202',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['146','147','148','149','150','151','152','153','154','155','156','157','200','201'])).

thf('203',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['203','204','205'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DzXip8fkru
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.25/1.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.25/1.44  % Solved by: fo/fo7.sh
% 1.25/1.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.25/1.44  % done 1437 iterations in 0.975s
% 1.25/1.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.25/1.44  % SZS output start Refutation
% 1.25/1.44  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.25/1.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.25/1.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.25/1.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.25/1.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.25/1.44  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.25/1.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.25/1.44  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.25/1.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.25/1.44  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.25/1.44  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.25/1.44  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.25/1.44  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.25/1.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.25/1.44  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.25/1.44  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.25/1.44  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.25/1.44  thf(sk_C_type, type, sk_C: $i).
% 1.25/1.44  thf(sk_B_type, type, sk_B: $i).
% 1.25/1.44  thf(sk_D_type, type, sk_D: $i).
% 1.25/1.44  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.25/1.44  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.25/1.44  thf(sk_A_type, type, sk_A: $i).
% 1.25/1.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.25/1.44  thf(t36_funct_2, conjecture,
% 1.25/1.44    (![A:$i,B:$i,C:$i]:
% 1.25/1.44     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.25/1.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.25/1.44       ( ![D:$i]:
% 1.25/1.44         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.25/1.44             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.25/1.44           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.25/1.44               ( r2_relset_1 @
% 1.25/1.44                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.25/1.44                 ( k6_partfun1 @ A ) ) & 
% 1.25/1.44               ( v2_funct_1 @ C ) ) =>
% 1.25/1.44             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.25/1.44               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.25/1.44  thf(zf_stmt_0, negated_conjecture,
% 1.25/1.44    (~( ![A:$i,B:$i,C:$i]:
% 1.25/1.44        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.25/1.44            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.25/1.44          ( ![D:$i]:
% 1.25/1.44            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.25/1.44                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.25/1.44              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.25/1.44                  ( r2_relset_1 @
% 1.25/1.44                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.25/1.44                    ( k6_partfun1 @ A ) ) & 
% 1.25/1.44                  ( v2_funct_1 @ C ) ) =>
% 1.25/1.44                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.25/1.44                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.25/1.44    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.25/1.44  thf('0', plain,
% 1.25/1.44      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.25/1.44        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.25/1.44        (k6_partfun1 @ sk_A))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf(redefinition_k6_partfun1, axiom,
% 1.25/1.44    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.25/1.44  thf('1', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 1.25/1.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.25/1.44  thf('2', plain,
% 1.25/1.44      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.25/1.44        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.25/1.44        (k6_relat_1 @ sk_A))),
% 1.25/1.44      inference('demod', [status(thm)], ['0', '1'])).
% 1.25/1.44  thf('3', plain,
% 1.25/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('4', plain,
% 1.25/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf(redefinition_k1_partfun1, axiom,
% 1.25/1.44    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.25/1.44     ( ( ( v1_funct_1 @ E ) & 
% 1.25/1.44         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.25/1.44         ( v1_funct_1 @ F ) & 
% 1.25/1.44         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.25/1.44       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.25/1.44  thf('5', plain,
% 1.25/1.44      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.25/1.44         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.25/1.44          | ~ (v1_funct_1 @ X31)
% 1.25/1.44          | ~ (v1_funct_1 @ X34)
% 1.25/1.44          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.25/1.44          | ((k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34)
% 1.25/1.44              = (k5_relat_1 @ X31 @ X34)))),
% 1.25/1.44      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.25/1.44  thf('6', plain,
% 1.25/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.25/1.44         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.25/1.44            = (k5_relat_1 @ sk_C @ X0))
% 1.25/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_1 @ sk_C))),
% 1.25/1.44      inference('sup-', [status(thm)], ['4', '5'])).
% 1.25/1.44  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('8', plain,
% 1.25/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.25/1.44         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.25/1.44            = (k5_relat_1 @ sk_C @ X0))
% 1.25/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.25/1.44          | ~ (v1_funct_1 @ X0))),
% 1.25/1.44      inference('demod', [status(thm)], ['6', '7'])).
% 1.25/1.44  thf('9', plain,
% 1.25/1.44      ((~ (v1_funct_1 @ sk_D)
% 1.25/1.44        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.25/1.44            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['3', '8'])).
% 1.25/1.44  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('11', plain,
% 1.25/1.44      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.25/1.44         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.25/1.44      inference('demod', [status(thm)], ['9', '10'])).
% 1.25/1.44  thf('12', plain,
% 1.25/1.44      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.25/1.44        (k6_relat_1 @ sk_A))),
% 1.25/1.44      inference('demod', [status(thm)], ['2', '11'])).
% 1.25/1.44  thf('13', plain,
% 1.25/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('14', plain,
% 1.25/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf(dt_k1_partfun1, axiom,
% 1.25/1.44    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.25/1.44     ( ( ( v1_funct_1 @ E ) & 
% 1.25/1.44         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.25/1.44         ( v1_funct_1 @ F ) & 
% 1.25/1.44         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.25/1.44       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.25/1.44         ( m1_subset_1 @
% 1.25/1.44           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.25/1.44           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.25/1.44  thf('15', plain,
% 1.25/1.44      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.25/1.44         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.25/1.44          | ~ (v1_funct_1 @ X23)
% 1.25/1.44          | ~ (v1_funct_1 @ X26)
% 1.25/1.44          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.25/1.44          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 1.25/1.44             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 1.25/1.44      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.25/1.44  thf('16', plain,
% 1.25/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.25/1.44         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.25/1.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.25/1.44          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.25/1.44          | ~ (v1_funct_1 @ X1)
% 1.25/1.44          | ~ (v1_funct_1 @ sk_C))),
% 1.25/1.44      inference('sup-', [status(thm)], ['14', '15'])).
% 1.25/1.44  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('18', plain,
% 1.25/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.25/1.44         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.25/1.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.25/1.44          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.25/1.44          | ~ (v1_funct_1 @ X1))),
% 1.25/1.44      inference('demod', [status(thm)], ['16', '17'])).
% 1.25/1.44  thf('19', plain,
% 1.25/1.44      ((~ (v1_funct_1 @ sk_D)
% 1.25/1.44        | (m1_subset_1 @ 
% 1.25/1.44           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.25/1.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.25/1.44      inference('sup-', [status(thm)], ['13', '18'])).
% 1.25/1.44  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('21', plain,
% 1.25/1.44      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.25/1.44         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.25/1.44      inference('demod', [status(thm)], ['9', '10'])).
% 1.25/1.44  thf('22', plain,
% 1.25/1.44      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.25/1.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.25/1.44      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.25/1.44  thf(redefinition_r2_relset_1, axiom,
% 1.25/1.44    (![A:$i,B:$i,C:$i,D:$i]:
% 1.25/1.44     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.25/1.44         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.25/1.44       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.25/1.44  thf('23', plain,
% 1.25/1.44      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.25/1.44         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.25/1.44          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.25/1.44          | ((X19) = (X22))
% 1.25/1.44          | ~ (r2_relset_1 @ X20 @ X21 @ X19 @ X22))),
% 1.25/1.44      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.25/1.44  thf('24', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.25/1.44          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.25/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.25/1.44      inference('sup-', [status(thm)], ['22', '23'])).
% 1.25/1.44  thf('25', plain,
% 1.25/1.44      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.25/1.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.25/1.44        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['12', '24'])).
% 1.25/1.44  thf(dt_k6_partfun1, axiom,
% 1.25/1.44    (![A:$i]:
% 1.25/1.44     ( ( m1_subset_1 @
% 1.25/1.44         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.25/1.44       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.25/1.44  thf('26', plain,
% 1.25/1.44      (![X30 : $i]:
% 1.25/1.44         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 1.25/1.44          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 1.25/1.44      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.25/1.44  thf('27', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 1.25/1.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.25/1.44  thf('28', plain,
% 1.25/1.44      (![X30 : $i]:
% 1.25/1.44         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 1.25/1.44          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 1.25/1.44      inference('demod', [status(thm)], ['26', '27'])).
% 1.25/1.44  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.25/1.44      inference('demod', [status(thm)], ['25', '28'])).
% 1.25/1.44  thf(t64_funct_1, axiom,
% 1.25/1.44    (![A:$i]:
% 1.25/1.44     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.25/1.44       ( ![B:$i]:
% 1.25/1.44         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.25/1.44           ( ( ( v2_funct_1 @ A ) & 
% 1.25/1.44               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.25/1.44               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.25/1.44             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.25/1.44  thf('30', plain,
% 1.25/1.44      (![X14 : $i, X15 : $i]:
% 1.25/1.44         (~ (v1_relat_1 @ X14)
% 1.25/1.44          | ~ (v1_funct_1 @ X14)
% 1.25/1.44          | ((X14) = (k2_funct_1 @ X15))
% 1.25/1.44          | ((k5_relat_1 @ X14 @ X15) != (k6_relat_1 @ (k2_relat_1 @ X15)))
% 1.25/1.44          | ((k2_relat_1 @ X14) != (k1_relat_1 @ X15))
% 1.25/1.44          | ~ (v2_funct_1 @ X15)
% 1.25/1.44          | ~ (v1_funct_1 @ X15)
% 1.25/1.44          | ~ (v1_relat_1 @ X15))),
% 1.25/1.44      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.25/1.44  thf('31', plain,
% 1.25/1.44      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 1.25/1.44        | ~ (v1_relat_1 @ sk_D)
% 1.25/1.44        | ~ (v1_funct_1 @ sk_D)
% 1.25/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.25/1.44        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.25/1.44        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.25/1.44        | ~ (v1_funct_1 @ sk_C)
% 1.25/1.44        | ~ (v1_relat_1 @ sk_C))),
% 1.25/1.44      inference('sup-', [status(thm)], ['29', '30'])).
% 1.25/1.44  thf('32', plain,
% 1.25/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf(cc2_relat_1, axiom,
% 1.25/1.44    (![A:$i]:
% 1.25/1.44     ( ( v1_relat_1 @ A ) =>
% 1.25/1.44       ( ![B:$i]:
% 1.25/1.44         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.25/1.44  thf('33', plain,
% 1.25/1.44      (![X0 : $i, X1 : $i]:
% 1.25/1.44         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.25/1.44          | (v1_relat_1 @ X0)
% 1.25/1.44          | ~ (v1_relat_1 @ X1))),
% 1.25/1.44      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.25/1.44  thf('34', plain,
% 1.25/1.44      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.25/1.44      inference('sup-', [status(thm)], ['32', '33'])).
% 1.25/1.44  thf(fc6_relat_1, axiom,
% 1.25/1.44    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.25/1.44  thf('35', plain,
% 1.25/1.44      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.25/1.44      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.25/1.44  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 1.25/1.44      inference('demod', [status(thm)], ['34', '35'])).
% 1.25/1.44  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('38', plain,
% 1.25/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf(redefinition_k2_relset_1, axiom,
% 1.25/1.44    (![A:$i,B:$i,C:$i]:
% 1.25/1.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.25/1.44       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.25/1.44  thf('39', plain,
% 1.25/1.44      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.25/1.44         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 1.25/1.44          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.25/1.44      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.25/1.44  thf('40', plain,
% 1.25/1.44      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.25/1.44      inference('sup-', [status(thm)], ['38', '39'])).
% 1.25/1.44  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('42', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.25/1.44      inference('sup+', [status(thm)], ['40', '41'])).
% 1.25/1.44  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('44', plain,
% 1.25/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('45', plain,
% 1.25/1.44      (![X0 : $i, X1 : $i]:
% 1.25/1.44         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.25/1.44          | (v1_relat_1 @ X0)
% 1.25/1.44          | ~ (v1_relat_1 @ X1))),
% 1.25/1.44      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.25/1.44  thf('46', plain,
% 1.25/1.44      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.25/1.44      inference('sup-', [status(thm)], ['44', '45'])).
% 1.25/1.44  thf('47', plain,
% 1.25/1.44      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.25/1.44      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.25/1.44  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 1.25/1.44      inference('demod', [status(thm)], ['46', '47'])).
% 1.25/1.44  thf('49', plain,
% 1.25/1.44      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 1.25/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.25/1.44        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.25/1.44        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.25/1.44      inference('demod', [status(thm)], ['31', '36', '37', '42', '43', '48'])).
% 1.25/1.44  thf('50', plain,
% 1.25/1.44      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.25/1.44         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.25/1.44      inference('demod', [status(thm)], ['9', '10'])).
% 1.25/1.44  thf('51', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.25/1.44      inference('demod', [status(thm)], ['25', '28'])).
% 1.25/1.44  thf('52', plain,
% 1.25/1.44      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.25/1.44         = (k6_relat_1 @ sk_A))),
% 1.25/1.44      inference('demod', [status(thm)], ['50', '51'])).
% 1.25/1.44  thf('53', plain,
% 1.25/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf(t24_funct_2, axiom,
% 1.25/1.44    (![A:$i,B:$i,C:$i]:
% 1.25/1.44     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.25/1.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.25/1.44       ( ![D:$i]:
% 1.25/1.44         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.25/1.44             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.25/1.44           ( ( r2_relset_1 @
% 1.25/1.44               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.25/1.44               ( k6_partfun1 @ B ) ) =>
% 1.25/1.44             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.25/1.44  thf('54', plain,
% 1.25/1.44      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.25/1.44         (~ (v1_funct_1 @ X38)
% 1.25/1.44          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 1.25/1.44          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.25/1.44          | ~ (r2_relset_1 @ X39 @ X39 @ 
% 1.25/1.44               (k1_partfun1 @ X39 @ X40 @ X40 @ X39 @ X38 @ X41) @ 
% 1.25/1.44               (k6_partfun1 @ X39))
% 1.25/1.44          | ((k2_relset_1 @ X40 @ X39 @ X41) = (X39))
% 1.25/1.44          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 1.25/1.44          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 1.25/1.44          | ~ (v1_funct_1 @ X41))),
% 1.25/1.44      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.25/1.44  thf('55', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 1.25/1.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.25/1.44  thf('56', plain,
% 1.25/1.44      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.25/1.44         (~ (v1_funct_1 @ X38)
% 1.25/1.44          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 1.25/1.44          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.25/1.44          | ~ (r2_relset_1 @ X39 @ X39 @ 
% 1.25/1.44               (k1_partfun1 @ X39 @ X40 @ X40 @ X39 @ X38 @ X41) @ 
% 1.25/1.44               (k6_relat_1 @ X39))
% 1.25/1.44          | ((k2_relset_1 @ X40 @ X39 @ X41) = (X39))
% 1.25/1.44          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 1.25/1.44          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 1.25/1.44          | ~ (v1_funct_1 @ X41))),
% 1.25/1.44      inference('demod', [status(thm)], ['54', '55'])).
% 1.25/1.44  thf('57', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (~ (v1_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.25/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.25/1.44          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.25/1.44          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.25/1.44               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.25/1.44               (k6_relat_1 @ sk_A))
% 1.25/1.44          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.25/1.44          | ~ (v1_funct_1 @ sk_C))),
% 1.25/1.44      inference('sup-', [status(thm)], ['53', '56'])).
% 1.25/1.44  thf('58', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('60', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (~ (v1_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.25/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.25/1.44          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.25/1.44          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.25/1.44               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.25/1.44               (k6_relat_1 @ sk_A)))),
% 1.25/1.44      inference('demod', [status(thm)], ['57', '58', '59'])).
% 1.25/1.44  thf('61', plain,
% 1.25/1.44      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.25/1.44           (k6_relat_1 @ sk_A))
% 1.25/1.44        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.25/1.44        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.25/1.44        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.25/1.44        | ~ (v1_funct_1 @ sk_D))),
% 1.25/1.44      inference('sup-', [status(thm)], ['52', '60'])).
% 1.25/1.44  thf('62', plain,
% 1.25/1.44      (![X30 : $i]:
% 1.25/1.44         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 1.25/1.44          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 1.25/1.44      inference('demod', [status(thm)], ['26', '27'])).
% 1.25/1.44  thf('63', plain,
% 1.25/1.44      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.25/1.44         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.25/1.44          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.25/1.44          | (r2_relset_1 @ X20 @ X21 @ X19 @ X22)
% 1.25/1.44          | ((X19) != (X22)))),
% 1.25/1.44      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.25/1.44  thf('64', plain,
% 1.25/1.44      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.25/1.44         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 1.25/1.44          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.25/1.44      inference('simplify', [status(thm)], ['63'])).
% 1.25/1.44  thf('65', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.25/1.44      inference('sup-', [status(thm)], ['62', '64'])).
% 1.25/1.44  thf('66', plain,
% 1.25/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('67', plain,
% 1.25/1.44      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.25/1.44         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 1.25/1.44          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.25/1.44      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.25/1.44  thf('68', plain,
% 1.25/1.44      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.25/1.44      inference('sup-', [status(thm)], ['66', '67'])).
% 1.25/1.44  thf('69', plain,
% 1.25/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('70', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('71', plain, ((v1_funct_1 @ sk_D)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('72', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.25/1.44      inference('demod', [status(thm)], ['61', '65', '68', '69', '70', '71'])).
% 1.25/1.44  thf('73', plain,
% 1.25/1.44      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 1.25/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.25/1.44        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.25/1.44        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.25/1.44      inference('demod', [status(thm)], ['49', '72'])).
% 1.25/1.44  thf('74', plain,
% 1.25/1.44      ((((sk_C) = (k2_funct_1 @ sk_D))
% 1.25/1.44        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.25/1.44        | ~ (v2_funct_1 @ sk_D))),
% 1.25/1.44      inference('simplify', [status(thm)], ['73'])).
% 1.25/1.44  thf('75', plain,
% 1.25/1.44      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.25/1.44         = (k6_relat_1 @ sk_A))),
% 1.25/1.44      inference('demod', [status(thm)], ['50', '51'])).
% 1.25/1.44  thf('76', plain,
% 1.25/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf(t30_funct_2, axiom,
% 1.25/1.44    (![A:$i,B:$i,C:$i,D:$i]:
% 1.25/1.44     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.25/1.44         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.25/1.44       ( ![E:$i]:
% 1.25/1.44         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.25/1.44             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.25/1.44           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.25/1.44               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.25/1.44             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.25/1.44               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.25/1.44  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.25/1.44  thf(zf_stmt_2, axiom,
% 1.25/1.44    (![C:$i,B:$i]:
% 1.25/1.44     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.25/1.44       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.25/1.44  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.25/1.44  thf(zf_stmt_4, axiom,
% 1.25/1.44    (![E:$i,D:$i]:
% 1.25/1.44     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.25/1.44  thf(zf_stmt_5, axiom,
% 1.25/1.44    (![A:$i,B:$i,C:$i,D:$i]:
% 1.25/1.44     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.25/1.44         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.25/1.44       ( ![E:$i]:
% 1.25/1.44         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.25/1.44             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.25/1.44           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.25/1.44               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.25/1.44             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.25/1.44  thf('77', plain,
% 1.25/1.44      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 1.25/1.44         (~ (v1_funct_1 @ X46)
% 1.25/1.44          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 1.25/1.44          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.25/1.44          | (zip_tseitin_0 @ X46 @ X49)
% 1.25/1.44          | ~ (v2_funct_1 @ (k1_partfun1 @ X50 @ X47 @ X47 @ X48 @ X49 @ X46))
% 1.25/1.44          | (zip_tseitin_1 @ X48 @ X47)
% 1.25/1.44          | ((k2_relset_1 @ X50 @ X47 @ X49) != (X47))
% 1.25/1.44          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X47)))
% 1.25/1.44          | ~ (v1_funct_2 @ X49 @ X50 @ X47)
% 1.25/1.44          | ~ (v1_funct_1 @ X49))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.25/1.44  thf('78', plain,
% 1.25/1.44      (![X0 : $i, X1 : $i]:
% 1.25/1.44         (~ (v1_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.25/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.25/1.44          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.25/1.44          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.25/1.44          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.25/1.44          | (zip_tseitin_0 @ sk_D @ X0)
% 1.25/1.44          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.25/1.44          | ~ (v1_funct_1 @ sk_D))),
% 1.25/1.44      inference('sup-', [status(thm)], ['76', '77'])).
% 1.25/1.44  thf('79', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('80', plain, ((v1_funct_1 @ sk_D)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('81', plain,
% 1.25/1.44      (![X0 : $i, X1 : $i]:
% 1.25/1.44         (~ (v1_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.25/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.25/1.44          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.25/1.44          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.25/1.44          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.25/1.44          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.25/1.44      inference('demod', [status(thm)], ['78', '79', '80'])).
% 1.25/1.44  thf('82', plain,
% 1.25/1.44      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.25/1.44        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.25/1.44        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.25/1.44        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.25/1.44        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.25/1.44        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.25/1.44        | ~ (v1_funct_1 @ sk_C))),
% 1.25/1.44      inference('sup-', [status(thm)], ['75', '81'])).
% 1.25/1.44  thf(fc4_funct_1, axiom,
% 1.25/1.44    (![A:$i]:
% 1.25/1.44     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.25/1.44       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.25/1.44  thf('83', plain, (![X10 : $i]: (v2_funct_1 @ (k6_relat_1 @ X10))),
% 1.25/1.44      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.25/1.44  thf('84', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('85', plain,
% 1.25/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('86', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('88', plain,
% 1.25/1.44      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.25/1.44        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.25/1.44        | ((sk_B) != (sk_B)))),
% 1.25/1.44      inference('demod', [status(thm)], ['82', '83', '84', '85', '86', '87'])).
% 1.25/1.44  thf('89', plain,
% 1.25/1.44      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.25/1.44      inference('simplify', [status(thm)], ['88'])).
% 1.25/1.44  thf('90', plain,
% 1.25/1.44      (![X44 : $i, X45 : $i]:
% 1.25/1.44         (((X44) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X44 @ X45))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.25/1.44  thf('91', plain,
% 1.25/1.44      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['89', '90'])).
% 1.25/1.44  thf('92', plain, (((sk_A) != (k1_xboole_0))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('93', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.25/1.44      inference('simplify_reflect-', [status(thm)], ['91', '92'])).
% 1.25/1.44  thf('94', plain,
% 1.25/1.44      (![X42 : $i, X43 : $i]:
% 1.25/1.44         ((v2_funct_1 @ X43) | ~ (zip_tseitin_0 @ X43 @ X42))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.25/1.44  thf('95', plain, ((v2_funct_1 @ sk_D)),
% 1.25/1.44      inference('sup-', [status(thm)], ['93', '94'])).
% 1.25/1.44  thf('96', plain,
% 1.25/1.44      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 1.25/1.44      inference('demod', [status(thm)], ['74', '95'])).
% 1.25/1.44  thf(t3_funct_2, axiom,
% 1.25/1.44    (![A:$i]:
% 1.25/1.44     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.25/1.44       ( ( v1_funct_1 @ A ) & 
% 1.25/1.44         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.25/1.44         ( m1_subset_1 @
% 1.25/1.44           A @ 
% 1.25/1.44           ( k1_zfmisc_1 @
% 1.25/1.44             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.25/1.44  thf('97', plain,
% 1.25/1.44      (![X54 : $i]:
% 1.25/1.44         ((m1_subset_1 @ X54 @ 
% 1.25/1.44           (k1_zfmisc_1 @ 
% 1.25/1.44            (k2_zfmisc_1 @ (k1_relat_1 @ X54) @ (k2_relat_1 @ X54))))
% 1.25/1.44          | ~ (v1_funct_1 @ X54)
% 1.25/1.44          | ~ (v1_relat_1 @ X54))),
% 1.25/1.44      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.25/1.44  thf('98', plain,
% 1.25/1.44      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.25/1.44         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 1.25/1.44          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.25/1.44      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.25/1.44  thf('99', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (~ (v1_relat_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.25/1.44              = (k2_relat_1 @ X0)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['97', '98'])).
% 1.25/1.44  thf('100', plain,
% 1.25/1.44      (![X54 : $i]:
% 1.25/1.44         ((v1_funct_2 @ X54 @ (k1_relat_1 @ X54) @ (k2_relat_1 @ X54))
% 1.25/1.44          | ~ (v1_funct_1 @ X54)
% 1.25/1.44          | ~ (v1_relat_1 @ X54))),
% 1.25/1.44      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.25/1.44  thf('101', plain,
% 1.25/1.44      (![X54 : $i]:
% 1.25/1.44         ((m1_subset_1 @ X54 @ 
% 1.25/1.44           (k1_zfmisc_1 @ 
% 1.25/1.44            (k2_zfmisc_1 @ (k1_relat_1 @ X54) @ (k2_relat_1 @ X54))))
% 1.25/1.44          | ~ (v1_funct_1 @ X54)
% 1.25/1.44          | ~ (v1_relat_1 @ X54))),
% 1.25/1.44      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.25/1.44  thf(t35_funct_2, axiom,
% 1.25/1.44    (![A:$i,B:$i,C:$i]:
% 1.25/1.44     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.25/1.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.25/1.44       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.25/1.44         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.25/1.44           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.25/1.44             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.25/1.44  thf('102', plain,
% 1.25/1.44      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.25/1.44         (((X51) = (k1_xboole_0))
% 1.25/1.44          | ~ (v1_funct_1 @ X52)
% 1.25/1.44          | ~ (v1_funct_2 @ X52 @ X53 @ X51)
% 1.25/1.44          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 1.25/1.44          | ((k5_relat_1 @ X52 @ (k2_funct_1 @ X52)) = (k6_partfun1 @ X53))
% 1.25/1.44          | ~ (v2_funct_1 @ X52)
% 1.25/1.44          | ((k2_relset_1 @ X53 @ X51 @ X52) != (X51)))),
% 1.25/1.44      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.25/1.44  thf('103', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 1.25/1.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.25/1.44  thf('104', plain,
% 1.25/1.44      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.25/1.44         (((X51) = (k1_xboole_0))
% 1.25/1.44          | ~ (v1_funct_1 @ X52)
% 1.25/1.44          | ~ (v1_funct_2 @ X52 @ X53 @ X51)
% 1.25/1.44          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 1.25/1.44          | ((k5_relat_1 @ X52 @ (k2_funct_1 @ X52)) = (k6_relat_1 @ X53))
% 1.25/1.44          | ~ (v2_funct_1 @ X52)
% 1.25/1.44          | ((k2_relset_1 @ X53 @ X51 @ X52) != (X51)))),
% 1.25/1.44      inference('demod', [status(thm)], ['102', '103'])).
% 1.25/1.44  thf('105', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (~ (v1_relat_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.25/1.44              != (k2_relat_1 @ X0))
% 1.25/1.44          | ~ (v2_funct_1 @ X0)
% 1.25/1.44          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.25/1.44              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.25/1.44          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['101', '104'])).
% 1.25/1.44  thf('106', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.25/1.44          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.25/1.44          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.25/1.44              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.25/1.44          | ~ (v2_funct_1 @ X0)
% 1.25/1.44          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.25/1.44              != (k2_relat_1 @ X0))
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_relat_1 @ X0))),
% 1.25/1.44      inference('simplify', [status(thm)], ['105'])).
% 1.25/1.44  thf('107', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (~ (v1_relat_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_relat_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.25/1.44              != (k2_relat_1 @ X0))
% 1.25/1.44          | ~ (v2_funct_1 @ X0)
% 1.25/1.44          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.25/1.44              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.25/1.44          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['100', '106'])).
% 1.25/1.44  thf('108', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.25/1.44          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.25/1.44              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.25/1.44          | ~ (v2_funct_1 @ X0)
% 1.25/1.44          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.25/1.44              != (k2_relat_1 @ X0))
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_relat_1 @ X0))),
% 1.25/1.44      inference('simplify', [status(thm)], ['107'])).
% 1.25/1.44  thf('109', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_relat_1 @ X0)
% 1.25/1.44          | ~ (v1_relat_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ~ (v2_funct_1 @ X0)
% 1.25/1.44          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.25/1.44              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.25/1.44          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['99', '108'])).
% 1.25/1.44  thf('110', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.25/1.44          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.25/1.44              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.25/1.44          | ~ (v2_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_relat_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_1 @ X0))),
% 1.25/1.44      inference('simplify', [status(thm)], ['109'])).
% 1.25/1.44  thf('111', plain,
% 1.25/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('112', plain,
% 1.25/1.44      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.25/1.44         (((X51) = (k1_xboole_0))
% 1.25/1.44          | ~ (v1_funct_1 @ X52)
% 1.25/1.44          | ~ (v1_funct_2 @ X52 @ X53 @ X51)
% 1.25/1.44          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 1.25/1.44          | ((k5_relat_1 @ X52 @ (k2_funct_1 @ X52)) = (k6_relat_1 @ X53))
% 1.25/1.44          | ~ (v2_funct_1 @ X52)
% 1.25/1.44          | ((k2_relset_1 @ X53 @ X51 @ X52) != (X51)))),
% 1.25/1.44      inference('demod', [status(thm)], ['102', '103'])).
% 1.25/1.44  thf('113', plain,
% 1.25/1.44      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.25/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.25/1.44        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.25/1.44        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.25/1.44        | ~ (v1_funct_1 @ sk_D)
% 1.25/1.44        | ((sk_A) = (k1_xboole_0)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['111', '112'])).
% 1.25/1.44  thf('114', plain,
% 1.25/1.44      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.25/1.44      inference('sup-', [status(thm)], ['66', '67'])).
% 1.25/1.44  thf('115', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('116', plain, ((v1_funct_1 @ sk_D)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('117', plain,
% 1.25/1.44      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.25/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.25/1.44        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.25/1.44        | ((sk_A) = (k1_xboole_0)))),
% 1.25/1.44      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 1.25/1.44  thf('118', plain, (((sk_A) != (k1_xboole_0))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('119', plain,
% 1.25/1.44      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.25/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.25/1.44        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 1.25/1.44      inference('simplify_reflect-', [status(thm)], ['117', '118'])).
% 1.25/1.44  thf('120', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.25/1.44      inference('demod', [status(thm)], ['61', '65', '68', '69', '70', '71'])).
% 1.25/1.44  thf('121', plain,
% 1.25/1.44      ((((sk_A) != (sk_A))
% 1.25/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.25/1.44        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 1.25/1.44      inference('demod', [status(thm)], ['119', '120'])).
% 1.25/1.44  thf('122', plain,
% 1.25/1.44      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.25/1.44        | ~ (v2_funct_1 @ sk_D))),
% 1.25/1.44      inference('simplify', [status(thm)], ['121'])).
% 1.25/1.44  thf('123', plain, ((v2_funct_1 @ sk_D)),
% 1.25/1.44      inference('sup-', [status(thm)], ['93', '94'])).
% 1.25/1.44  thf('124', plain,
% 1.25/1.44      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.25/1.44      inference('demod', [status(thm)], ['122', '123'])).
% 1.25/1.44  thf('125', plain,
% 1.25/1.44      ((((k6_relat_1 @ (k1_relat_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.25/1.44        | ~ (v1_funct_1 @ sk_D)
% 1.25/1.44        | ~ (v1_relat_1 @ sk_D)
% 1.25/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.25/1.44        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.25/1.44      inference('sup+', [status(thm)], ['110', '124'])).
% 1.25/1.44  thf('126', plain, ((v1_funct_1 @ sk_D)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('127', plain, ((v1_relat_1 @ sk_D)),
% 1.25/1.44      inference('demod', [status(thm)], ['34', '35'])).
% 1.25/1.44  thf('128', plain, ((v2_funct_1 @ sk_D)),
% 1.25/1.44      inference('sup-', [status(thm)], ['93', '94'])).
% 1.25/1.44  thf('129', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.25/1.44      inference('demod', [status(thm)], ['61', '65', '68', '69', '70', '71'])).
% 1.25/1.44  thf('130', plain,
% 1.25/1.44      ((((k6_relat_1 @ (k1_relat_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.25/1.44        | ((sk_A) = (k1_xboole_0)))),
% 1.25/1.44      inference('demod', [status(thm)], ['125', '126', '127', '128', '129'])).
% 1.25/1.44  thf('131', plain, (((sk_A) != (k1_xboole_0))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('132', plain,
% 1.25/1.44      (((k6_relat_1 @ (k1_relat_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.25/1.44      inference('simplify_reflect-', [status(thm)], ['130', '131'])).
% 1.25/1.44  thf(t71_relat_1, axiom,
% 1.25/1.44    (![A:$i]:
% 1.25/1.44     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.25/1.44       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.25/1.44  thf('133', plain, (![X6 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 1.25/1.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.25/1.44  thf('134', plain,
% 1.25/1.44      (((k1_relat_1 @ (k6_relat_1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 1.25/1.44      inference('sup+', [status(thm)], ['132', '133'])).
% 1.25/1.44  thf('135', plain, (![X6 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 1.25/1.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.25/1.44  thf('136', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.25/1.44      inference('demod', [status(thm)], ['134', '135'])).
% 1.25/1.44  thf('137', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 1.25/1.44      inference('demod', [status(thm)], ['96', '136'])).
% 1.25/1.44  thf('138', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.25/1.44      inference('simplify', [status(thm)], ['137'])).
% 1.25/1.44  thf(t55_funct_1, axiom,
% 1.25/1.44    (![A:$i]:
% 1.25/1.44     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.25/1.44       ( ( v2_funct_1 @ A ) =>
% 1.25/1.44         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.25/1.44           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.25/1.44  thf('139', plain,
% 1.25/1.44      (![X13 : $i]:
% 1.25/1.44         (~ (v2_funct_1 @ X13)
% 1.25/1.44          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 1.25/1.44          | ~ (v1_funct_1 @ X13)
% 1.25/1.44          | ~ (v1_relat_1 @ X13))),
% 1.25/1.44      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.25/1.44  thf('140', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.25/1.44          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.25/1.44              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.25/1.44          | ~ (v2_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_relat_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_1 @ X0))),
% 1.25/1.44      inference('simplify', [status(thm)], ['109'])).
% 1.25/1.44  thf('141', plain,
% 1.25/1.44      (![X14 : $i, X15 : $i]:
% 1.25/1.44         (~ (v1_relat_1 @ X14)
% 1.25/1.44          | ~ (v1_funct_1 @ X14)
% 1.25/1.44          | ((X14) = (k2_funct_1 @ X15))
% 1.25/1.44          | ((k5_relat_1 @ X14 @ X15) != (k6_relat_1 @ (k2_relat_1 @ X15)))
% 1.25/1.44          | ((k2_relat_1 @ X14) != (k1_relat_1 @ X15))
% 1.25/1.44          | ~ (v2_funct_1 @ X15)
% 1.25/1.44          | ~ (v1_funct_1 @ X15)
% 1.25/1.44          | ~ (v1_relat_1 @ X15))),
% 1.25/1.44      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.25/1.44  thf('142', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 1.25/1.44            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_relat_1 @ X0)
% 1.25/1.44          | ~ (v2_funct_1 @ X0)
% 1.25/1.44          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.25/1.44          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.25/1.44          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.25/1.44          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.25/1.44          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.25/1.44          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_relat_1 @ X0))),
% 1.25/1.44      inference('sup-', [status(thm)], ['140', '141'])).
% 1.25/1.44  thf('143', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.25/1.44          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.25/1.44          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.25/1.44          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.25/1.44          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.25/1.44          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.25/1.44          | ~ (v2_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_relat_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 1.25/1.44              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.25/1.44      inference('simplify', [status(thm)], ['142'])).
% 1.25/1.44  thf('144', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (((k6_relat_1 @ (k1_relat_1 @ X0)) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.25/1.44          | ~ (v1_relat_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ~ (v2_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_relat_1 @ X0)
% 1.25/1.44          | ~ (v2_funct_1 @ X0)
% 1.25/1.44          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.25/1.44          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.25/1.44          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.25/1.44          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.25/1.44          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.25/1.44          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.25/1.44      inference('sup-', [status(thm)], ['139', '143'])).
% 1.25/1.44  thf('145', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.25/1.44          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.25/1.44          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.25/1.44          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.25/1.44          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.25/1.44          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.25/1.44          | ~ (v2_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ~ (v1_relat_1 @ X0))),
% 1.25/1.44      inference('simplify', [status(thm)], ['144'])).
% 1.25/1.44  thf('146', plain,
% 1.25/1.44      ((~ (v2_funct_1 @ sk_C)
% 1.25/1.44        | ~ (v1_relat_1 @ sk_D)
% 1.25/1.44        | ~ (v1_funct_1 @ sk_D)
% 1.25/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.25/1.44        | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 1.25/1.44        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 1.25/1.44        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 1.25/1.44        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 1.25/1.44        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 1.25/1.44      inference('sup-', [status(thm)], ['138', '145'])).
% 1.25/1.44  thf('147', plain, ((v2_funct_1 @ sk_C)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('148', plain, ((v1_relat_1 @ sk_D)),
% 1.25/1.44      inference('demod', [status(thm)], ['34', '35'])).
% 1.25/1.44  thf('149', plain, ((v1_funct_1 @ sk_D)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('150', plain, ((v2_funct_1 @ sk_D)),
% 1.25/1.44      inference('sup-', [status(thm)], ['93', '94'])).
% 1.25/1.44  thf('151', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.25/1.44      inference('demod', [status(thm)], ['61', '65', '68', '69', '70', '71'])).
% 1.25/1.44  thf('152', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.25/1.44      inference('simplify', [status(thm)], ['137'])).
% 1.25/1.44  thf('153', plain, ((v1_relat_1 @ sk_C)),
% 1.25/1.44      inference('demod', [status(thm)], ['46', '47'])).
% 1.25/1.44  thf('154', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.25/1.44      inference('simplify', [status(thm)], ['137'])).
% 1.25/1.44  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('156', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.25/1.44      inference('demod', [status(thm)], ['61', '65', '68', '69', '70', '71'])).
% 1.25/1.44  thf('157', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.25/1.44      inference('simplify', [status(thm)], ['137'])).
% 1.25/1.44  thf('158', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.25/1.44      inference('sup+', [status(thm)], ['40', '41'])).
% 1.25/1.44  thf('159', plain,
% 1.25/1.44      (![X54 : $i]:
% 1.25/1.44         ((m1_subset_1 @ X54 @ 
% 1.25/1.44           (k1_zfmisc_1 @ 
% 1.25/1.44            (k2_zfmisc_1 @ (k1_relat_1 @ X54) @ (k2_relat_1 @ X54))))
% 1.25/1.44          | ~ (v1_funct_1 @ X54)
% 1.25/1.44          | ~ (v1_relat_1 @ X54))),
% 1.25/1.44      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.25/1.44  thf('160', plain,
% 1.25/1.44      (((m1_subset_1 @ sk_C @ 
% 1.25/1.44         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))
% 1.25/1.44        | ~ (v1_relat_1 @ sk_C)
% 1.25/1.44        | ~ (v1_funct_1 @ sk_C))),
% 1.25/1.44      inference('sup+', [status(thm)], ['158', '159'])).
% 1.25/1.44  thf('161', plain, ((v1_relat_1 @ sk_C)),
% 1.25/1.44      inference('demod', [status(thm)], ['46', '47'])).
% 1.25/1.44  thf('162', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('163', plain,
% 1.25/1.44      ((m1_subset_1 @ sk_C @ 
% 1.25/1.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 1.25/1.44      inference('demod', [status(thm)], ['160', '161', '162'])).
% 1.25/1.44  thf('164', plain,
% 1.25/1.44      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.25/1.44         (((X51) = (k1_xboole_0))
% 1.25/1.44          | ~ (v1_funct_1 @ X52)
% 1.25/1.44          | ~ (v1_funct_2 @ X52 @ X53 @ X51)
% 1.25/1.44          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 1.25/1.44          | ((k5_relat_1 @ X52 @ (k2_funct_1 @ X52)) = (k6_relat_1 @ X53))
% 1.25/1.44          | ~ (v2_funct_1 @ X52)
% 1.25/1.44          | ((k2_relset_1 @ X53 @ X51 @ X52) != (X51)))),
% 1.25/1.44      inference('demod', [status(thm)], ['102', '103'])).
% 1.25/1.44  thf('165', plain,
% 1.25/1.44      ((((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C) != (sk_B))
% 1.25/1.44        | ~ (v2_funct_1 @ sk_C)
% 1.25/1.44        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.25/1.44            = (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 1.25/1.44        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)
% 1.25/1.44        | ~ (v1_funct_1 @ sk_C)
% 1.25/1.44        | ((sk_B) = (k1_xboole_0)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['163', '164'])).
% 1.25/1.44  thf('166', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.25/1.44      inference('sup+', [status(thm)], ['40', '41'])).
% 1.25/1.44  thf('167', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (~ (v1_relat_1 @ X0)
% 1.25/1.44          | ~ (v1_funct_1 @ X0)
% 1.25/1.44          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.25/1.44              = (k2_relat_1 @ X0)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['97', '98'])).
% 1.25/1.44  thf('168', plain,
% 1.25/1.44      ((((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C)
% 1.25/1.44          = (k2_relat_1 @ sk_C))
% 1.25/1.44        | ~ (v1_funct_1 @ sk_C)
% 1.25/1.44        | ~ (v1_relat_1 @ sk_C))),
% 1.25/1.44      inference('sup+', [status(thm)], ['166', '167'])).
% 1.25/1.44  thf('169', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.25/1.44      inference('sup+', [status(thm)], ['40', '41'])).
% 1.25/1.44  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('171', plain, ((v1_relat_1 @ sk_C)),
% 1.25/1.44      inference('demod', [status(thm)], ['46', '47'])).
% 1.25/1.44  thf('172', plain,
% 1.25/1.44      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C) = (sk_B))),
% 1.25/1.44      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 1.25/1.44  thf('173', plain, ((v2_funct_1 @ sk_C)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('174', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.25/1.44      inference('sup+', [status(thm)], ['40', '41'])).
% 1.25/1.44  thf('175', plain,
% 1.25/1.44      (![X54 : $i]:
% 1.25/1.44         ((v1_funct_2 @ X54 @ (k1_relat_1 @ X54) @ (k2_relat_1 @ X54))
% 1.25/1.44          | ~ (v1_funct_1 @ X54)
% 1.25/1.44          | ~ (v1_relat_1 @ X54))),
% 1.25/1.44      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.25/1.44  thf('176', plain,
% 1.25/1.44      (((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)
% 1.25/1.44        | ~ (v1_relat_1 @ sk_C)
% 1.25/1.44        | ~ (v1_funct_1 @ sk_C))),
% 1.25/1.44      inference('sup+', [status(thm)], ['174', '175'])).
% 1.25/1.44  thf('177', plain, ((v1_relat_1 @ sk_C)),
% 1.25/1.44      inference('demod', [status(thm)], ['46', '47'])).
% 1.25/1.44  thf('178', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('179', plain, ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)),
% 1.25/1.44      inference('demod', [status(thm)], ['176', '177', '178'])).
% 1.25/1.44  thf('180', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('181', plain,
% 1.25/1.44      ((((sk_B) != (sk_B))
% 1.25/1.44        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.25/1.44            = (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 1.25/1.44        | ((sk_B) = (k1_xboole_0)))),
% 1.25/1.44      inference('demod', [status(thm)], ['165', '172', '173', '179', '180'])).
% 1.25/1.44  thf('182', plain,
% 1.25/1.44      ((((sk_B) = (k1_xboole_0))
% 1.25/1.44        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.25/1.44            = (k6_relat_1 @ (k1_relat_1 @ sk_C))))),
% 1.25/1.44      inference('simplify', [status(thm)], ['181'])).
% 1.25/1.44  thf('183', plain, (((sk_B) != (k1_xboole_0))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('184', plain,
% 1.25/1.44      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.25/1.44         = (k6_relat_1 @ (k1_relat_1 @ sk_C)))),
% 1.25/1.44      inference('simplify_reflect-', [status(thm)], ['182', '183'])).
% 1.25/1.44  thf('185', plain,
% 1.25/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('186', plain,
% 1.25/1.44      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.25/1.44         (((X51) = (k1_xboole_0))
% 1.25/1.44          | ~ (v1_funct_1 @ X52)
% 1.25/1.44          | ~ (v1_funct_2 @ X52 @ X53 @ X51)
% 1.25/1.44          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 1.25/1.44          | ((k5_relat_1 @ X52 @ (k2_funct_1 @ X52)) = (k6_relat_1 @ X53))
% 1.25/1.44          | ~ (v2_funct_1 @ X52)
% 1.25/1.44          | ((k2_relset_1 @ X53 @ X51 @ X52) != (X51)))),
% 1.25/1.44      inference('demod', [status(thm)], ['102', '103'])).
% 1.25/1.44  thf('187', plain,
% 1.25/1.44      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.25/1.44        | ~ (v2_funct_1 @ sk_C)
% 1.25/1.44        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.25/1.44        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.25/1.44        | ~ (v1_funct_1 @ sk_C)
% 1.25/1.44        | ((sk_B) = (k1_xboole_0)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['185', '186'])).
% 1.25/1.44  thf('188', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('189', plain, ((v2_funct_1 @ sk_C)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('190', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('192', plain,
% 1.25/1.44      ((((sk_B) != (sk_B))
% 1.25/1.44        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.25/1.44        | ((sk_B) = (k1_xboole_0)))),
% 1.25/1.44      inference('demod', [status(thm)], ['187', '188', '189', '190', '191'])).
% 1.25/1.44  thf('193', plain,
% 1.25/1.44      ((((sk_B) = (k1_xboole_0))
% 1.25/1.44        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 1.25/1.44      inference('simplify', [status(thm)], ['192'])).
% 1.25/1.44  thf('194', plain, (((sk_B) != (k1_xboole_0))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('195', plain,
% 1.25/1.44      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 1.25/1.44      inference('simplify_reflect-', [status(thm)], ['193', '194'])).
% 1.25/1.44  thf('196', plain,
% 1.25/1.44      (((k6_relat_1 @ (k1_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 1.25/1.44      inference('sup+', [status(thm)], ['184', '195'])).
% 1.25/1.44  thf('197', plain, (![X6 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 1.25/1.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.25/1.44  thf('198', plain,
% 1.25/1.44      (((k1_relat_1 @ (k6_relat_1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 1.25/1.44      inference('sup+', [status(thm)], ['196', '197'])).
% 1.25/1.44  thf('199', plain, (![X6 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 1.25/1.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.25/1.44  thf('200', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.25/1.44      inference('demod', [status(thm)], ['198', '199'])).
% 1.25/1.44  thf('201', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.25/1.44      inference('simplify', [status(thm)], ['137'])).
% 1.25/1.44  thf('202', plain,
% 1.25/1.44      ((((sk_A) = (k1_xboole_0))
% 1.25/1.44        | ((sk_A) != (sk_A))
% 1.25/1.44        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.25/1.44      inference('demod', [status(thm)],
% 1.25/1.44                ['146', '147', '148', '149', '150', '151', '152', '153', 
% 1.25/1.44                 '154', '155', '156', '157', '200', '201'])).
% 1.25/1.44  thf('203', plain,
% 1.25/1.44      ((((sk_D) = (k2_funct_1 @ sk_C)) | ((sk_A) = (k1_xboole_0)))),
% 1.25/1.44      inference('simplify', [status(thm)], ['202'])).
% 1.25/1.44  thf('204', plain, (((sk_A) != (k1_xboole_0))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('205', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('206', plain, ($false),
% 1.25/1.44      inference('simplify_reflect-', [status(thm)], ['203', '204', '205'])).
% 1.25/1.44  
% 1.25/1.44  % SZS output end Refutation
% 1.25/1.44  
% 1.25/1.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
