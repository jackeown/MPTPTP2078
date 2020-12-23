%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jSSKDie9Yn

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:06 EST 2020

% Result     : Theorem 3.50s
% Output     : Refutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  246 ( 999 expanded)
%              Number of leaves         :   48 ( 302 expanded)
%              Depth                    :   42
%              Number of atoms          : 3032 (25838 expanded)
%              Number of equality atoms :  174 (1676 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
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
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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
      ( ( ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0 )
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
      ( ( ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A_1 ) ) ),
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
    = ( k6_relat_1 @ sk_A_1 ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k2_funct_1 @ X12 ) )
      | ( ( k5_relat_1 @ X11 @ X12 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('31',plain,
    ( ( ( k6_relat_1 @ sk_A_1 )
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

thf('32',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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

thf('34',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( r2_relset_1 @ X40 @ X40 @ ( k1_partfun1 @ X40 @ X41 @ X41 @ X40 @ X39 @ X42 ) @ ( k6_partfun1 @ X40 ) )
      | ( ( k2_relset_1 @ X41 @ X40 @ X42 )
        = X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('35',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( r2_relset_1 @ X40 @ X40 @ ( k1_partfun1 @ X40 @ X41 @ X41 @ X40 @ X39 @ X42 ) @ ( k6_relat_1 @ X40 ) )
      | ( ( k2_relset_1 @ X41 @ X40 @ X42 )
        = X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ X0 )
        = sk_A_1 )
      | ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A_1 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ X0 )
        = sk_A_1 )
      | ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A_1 ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
      = sk_A_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['41','42','45','46','47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('51',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('52',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k6_relat_1 @ sk_A_1 )
     != ( k6_relat_1 @ sk_A_1 ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','49','52','53','58','59','62'])).

thf('64',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('66',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('67',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
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

thf('69',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( zip_tseitin_0 @ X47 @ X50 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X51 @ X48 @ X48 @ X49 @ X50 @ X47 ) )
      | ( zip_tseitin_1 @ X49 @ X48 )
      | ( ( k2_relset_1 @ X51 @ X48 @ X50 )
       != X48 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X48 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A_1 ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('75',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('76',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['74','75','76','77','78','79'])).

thf('81',plain,
    ( ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('83',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X43: $i,X44: $i] :
      ( ( v2_funct_1 @ X44 )
      | ~ ( zip_tseitin_0 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('87',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
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

thf('90',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X52 ) ) )
      | ( ( k5_relat_1 @ X53 @ ( k2_funct_1 @ X53 ) )
        = ( k6_partfun1 @ X54 ) )
      | ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X54 @ X52 @ X53 )
       != X52 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('91',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('92',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X52 ) ) )
      | ( ( k5_relat_1 @ X53 @ ( k2_funct_1 @ X53 ) )
        = ( k6_relat_1 @ X54 ) )
      | ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X54 @ X52 @ X53 )
       != X52 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('95',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['41','42','45','46','47','48'])).

thf('101',plain,
    ( ( sk_A_1 != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('104',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('105',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('106',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('107',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('108',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('109',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('110',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('111',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('112',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('113',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('114',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('115',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('116',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('117',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t59_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('118',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 ) )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['115','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['114','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['113','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['112','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['111','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['110','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('134',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('135',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('137',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['135','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['134','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['133','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['132','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('148',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('149',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('150',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('151',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('152',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('153',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('154',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('155',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 ) )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['152','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['151','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['150','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['149','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['148','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['146','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['108','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['107','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['106','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['105','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['104','180'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('182',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('183',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['50','51'])).

thf('184',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('186',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['181','182','183','184','185'])).

thf('187',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['88','186'])).

thf('188',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('190',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['50','51'])).

thf('192',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('194',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['190','191','192','193'])).

thf('195',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['194','195'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jSSKDie9Yn
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.50/3.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.50/3.71  % Solved by: fo/fo7.sh
% 3.50/3.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.50/3.71  % done 2533 iterations in 3.246s
% 3.50/3.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.50/3.71  % SZS output start Refutation
% 3.50/3.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.50/3.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.50/3.71  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.50/3.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.50/3.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 3.50/3.71  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.50/3.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.50/3.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.50/3.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.50/3.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.50/3.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.50/3.71  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.50/3.71  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.50/3.71  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.50/3.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.50/3.71  thf(sk_C_type, type, sk_C: $i).
% 3.50/3.71  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.50/3.71  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.50/3.71  thf(sk_B_type, type, sk_B: $i).
% 3.50/3.71  thf(sk_D_type, type, sk_D: $i).
% 3.50/3.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.50/3.71  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.50/3.71  thf(sk_A_1_type, type, sk_A_1: $i).
% 3.50/3.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.50/3.71  thf(t36_funct_2, conjecture,
% 3.50/3.71    (![A:$i,B:$i,C:$i]:
% 3.50/3.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.50/3.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.50/3.71       ( ![D:$i]:
% 3.50/3.71         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.50/3.71             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.50/3.71           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 3.50/3.71               ( r2_relset_1 @
% 3.50/3.71                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.50/3.71                 ( k6_partfun1 @ A ) ) & 
% 3.50/3.71               ( v2_funct_1 @ C ) ) =>
% 3.50/3.71             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.50/3.71               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 3.50/3.71  thf(zf_stmt_0, negated_conjecture,
% 3.50/3.71    (~( ![A:$i,B:$i,C:$i]:
% 3.50/3.71        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.50/3.71            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.50/3.71          ( ![D:$i]:
% 3.50/3.71            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.50/3.71                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.50/3.71              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 3.50/3.71                  ( r2_relset_1 @
% 3.50/3.71                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.50/3.71                    ( k6_partfun1 @ A ) ) & 
% 3.50/3.71                  ( v2_funct_1 @ C ) ) =>
% 3.50/3.71                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.50/3.71                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 3.50/3.71    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 3.50/3.71  thf('0', plain,
% 3.50/3.71      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 3.50/3.71        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 3.50/3.71        (k6_partfun1 @ sk_A_1))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf(redefinition_k6_partfun1, axiom,
% 3.50/3.71    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.50/3.71  thf('1', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 3.50/3.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.50/3.71  thf('2', plain,
% 3.50/3.71      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 3.50/3.71        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 3.50/3.71        (k6_relat_1 @ sk_A_1))),
% 3.50/3.71      inference('demod', [status(thm)], ['0', '1'])).
% 3.50/3.71  thf('3', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('4', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf(redefinition_k1_partfun1, axiom,
% 3.50/3.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.50/3.71     ( ( ( v1_funct_1 @ E ) & 
% 3.50/3.71         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.50/3.71         ( v1_funct_1 @ F ) & 
% 3.50/3.71         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.50/3.71       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.50/3.71  thf('5', plain,
% 3.50/3.71      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 3.50/3.71         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 3.50/3.71          | ~ (v1_funct_1 @ X32)
% 3.50/3.71          | ~ (v1_funct_1 @ X35)
% 3.50/3.71          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 3.50/3.71          | ((k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 3.50/3.71              = (k5_relat_1 @ X32 @ X35)))),
% 3.50/3.71      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.50/3.71  thf('6', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.50/3.71            = (k5_relat_1 @ sk_C @ X0))
% 3.50/3.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ sk_C))),
% 3.50/3.71      inference('sup-', [status(thm)], ['4', '5'])).
% 3.50/3.71  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('8', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.50/3.71            = (k5_relat_1 @ sk_C @ X0))
% 3.50/3.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.50/3.71          | ~ (v1_funct_1 @ X0))),
% 3.50/3.71      inference('demod', [status(thm)], ['6', '7'])).
% 3.50/3.71  thf('9', plain,
% 3.50/3.71      ((~ (v1_funct_1 @ sk_D)
% 3.50/3.71        | ((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 3.50/3.71            = (k5_relat_1 @ sk_C @ sk_D)))),
% 3.50/3.71      inference('sup-', [status(thm)], ['3', '8'])).
% 3.50/3.71  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('11', plain,
% 3.50/3.71      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 3.50/3.71         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.50/3.71      inference('demod', [status(thm)], ['9', '10'])).
% 3.50/3.71  thf('12', plain,
% 3.50/3.71      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.50/3.71        (k6_relat_1 @ sk_A_1))),
% 3.50/3.71      inference('demod', [status(thm)], ['2', '11'])).
% 3.50/3.71  thf('13', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('14', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf(dt_k1_partfun1, axiom,
% 3.50/3.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.50/3.71     ( ( ( v1_funct_1 @ E ) & 
% 3.50/3.71         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.50/3.71         ( v1_funct_1 @ F ) & 
% 3.50/3.71         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.50/3.71       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.50/3.71         ( m1_subset_1 @
% 3.50/3.71           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.50/3.71           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.50/3.71  thf('15', plain,
% 3.50/3.71      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.50/3.71         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.50/3.71          | ~ (v1_funct_1 @ X24)
% 3.50/3.71          | ~ (v1_funct_1 @ X27)
% 3.50/3.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.50/3.71          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 3.50/3.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 3.50/3.71      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.50/3.71  thf('16', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.50/3.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 3.50/3.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.50/3.71          | ~ (v1_funct_1 @ X1)
% 3.50/3.71          | ~ (v1_funct_1 @ sk_C))),
% 3.50/3.71      inference('sup-', [status(thm)], ['14', '15'])).
% 3.50/3.71  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('18', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.50/3.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 3.50/3.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.50/3.71          | ~ (v1_funct_1 @ X1))),
% 3.50/3.71      inference('demod', [status(thm)], ['16', '17'])).
% 3.50/3.71  thf('19', plain,
% 3.50/3.71      ((~ (v1_funct_1 @ sk_D)
% 3.50/3.71        | (m1_subset_1 @ 
% 3.50/3.71           (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 3.50/3.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['13', '18'])).
% 3.50/3.71  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('21', plain,
% 3.50/3.71      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 3.50/3.71         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.50/3.71      inference('demod', [status(thm)], ['9', '10'])).
% 3.50/3.71  thf('22', plain,
% 3.50/3.71      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.50/3.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))),
% 3.50/3.71      inference('demod', [status(thm)], ['19', '20', '21'])).
% 3.50/3.71  thf(redefinition_r2_relset_1, axiom,
% 3.50/3.71    (![A:$i,B:$i,C:$i,D:$i]:
% 3.50/3.71     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.50/3.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.50/3.71       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.50/3.71  thf('23', plain,
% 3.50/3.71      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 3.50/3.71         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 3.50/3.71          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 3.50/3.71          | ((X20) = (X23))
% 3.50/3.71          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 3.50/3.71      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.50/3.71  thf('24', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 3.50/3.71          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 3.50/3.71          | ~ (m1_subset_1 @ X0 @ 
% 3.50/3.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['22', '23'])).
% 3.50/3.71  thf('25', plain,
% 3.50/3.71      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A_1) @ 
% 3.50/3.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))
% 3.50/3.71        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A_1)))),
% 3.50/3.71      inference('sup-', [status(thm)], ['12', '24'])).
% 3.50/3.71  thf(dt_k6_partfun1, axiom,
% 3.50/3.71    (![A:$i]:
% 3.50/3.71     ( ( m1_subset_1 @
% 3.50/3.71         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.50/3.71       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.50/3.71  thf('26', plain,
% 3.50/3.71      (![X31 : $i]:
% 3.50/3.71         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 3.50/3.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 3.50/3.71      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.50/3.71  thf('27', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 3.50/3.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.50/3.71  thf('28', plain,
% 3.50/3.71      (![X31 : $i]:
% 3.50/3.71         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 3.50/3.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 3.50/3.71      inference('demod', [status(thm)], ['26', '27'])).
% 3.50/3.71  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A_1))),
% 3.50/3.71      inference('demod', [status(thm)], ['25', '28'])).
% 3.50/3.71  thf(t64_funct_1, axiom,
% 3.50/3.71    (![A:$i]:
% 3.50/3.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.50/3.71       ( ![B:$i]:
% 3.50/3.71         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.50/3.71           ( ( ( v2_funct_1 @ A ) & 
% 3.50/3.71               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 3.50/3.71               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 3.50/3.71             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.50/3.71  thf('30', plain,
% 3.50/3.71      (![X11 : $i, X12 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X11)
% 3.50/3.71          | ~ (v1_funct_1 @ X11)
% 3.50/3.71          | ((X11) = (k2_funct_1 @ X12))
% 3.50/3.71          | ((k5_relat_1 @ X11 @ X12) != (k6_relat_1 @ (k2_relat_1 @ X12)))
% 3.50/3.71          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X12))
% 3.50/3.71          | ~ (v2_funct_1 @ X12)
% 3.50/3.71          | ~ (v1_funct_1 @ X12)
% 3.50/3.71          | ~ (v1_relat_1 @ X12))),
% 3.50/3.71      inference('cnf', [status(esa)], [t64_funct_1])).
% 3.50/3.71  thf('31', plain,
% 3.50/3.71      ((((k6_relat_1 @ sk_A_1) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 3.50/3.71        | ~ (v1_relat_1 @ sk_D)
% 3.50/3.71        | ~ (v1_funct_1 @ sk_D)
% 3.50/3.71        | ~ (v2_funct_1 @ sk_D)
% 3.50/3.71        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 3.50/3.71        | ((sk_C) = (k2_funct_1 @ sk_D))
% 3.50/3.71        | ~ (v1_funct_1 @ sk_C)
% 3.50/3.71        | ~ (v1_relat_1 @ sk_C))),
% 3.50/3.71      inference('sup-', [status(thm)], ['29', '30'])).
% 3.50/3.71  thf('32', plain,
% 3.50/3.71      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 3.50/3.71         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.50/3.71      inference('demod', [status(thm)], ['9', '10'])).
% 3.50/3.71  thf('33', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf(t24_funct_2, axiom,
% 3.50/3.71    (![A:$i,B:$i,C:$i]:
% 3.50/3.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.50/3.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.50/3.71       ( ![D:$i]:
% 3.50/3.71         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.50/3.71             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.50/3.71           ( ( r2_relset_1 @
% 3.50/3.71               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.50/3.71               ( k6_partfun1 @ B ) ) =>
% 3.50/3.71             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.50/3.71  thf('34', plain,
% 3.50/3.71      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 3.50/3.71         (~ (v1_funct_1 @ X39)
% 3.50/3.71          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 3.50/3.71          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.50/3.71          | ~ (r2_relset_1 @ X40 @ X40 @ 
% 3.50/3.71               (k1_partfun1 @ X40 @ X41 @ X41 @ X40 @ X39 @ X42) @ 
% 3.50/3.71               (k6_partfun1 @ X40))
% 3.50/3.71          | ((k2_relset_1 @ X41 @ X40 @ X42) = (X40))
% 3.50/3.71          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 3.50/3.71          | ~ (v1_funct_2 @ X42 @ X41 @ X40)
% 3.50/3.71          | ~ (v1_funct_1 @ X42))),
% 3.50/3.71      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.50/3.71  thf('35', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 3.50/3.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.50/3.71  thf('36', plain,
% 3.50/3.71      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 3.50/3.71         (~ (v1_funct_1 @ X39)
% 3.50/3.71          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 3.50/3.71          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.50/3.71          | ~ (r2_relset_1 @ X40 @ X40 @ 
% 3.50/3.71               (k1_partfun1 @ X40 @ X41 @ X41 @ X40 @ X39 @ X42) @ 
% 3.50/3.71               (k6_relat_1 @ X40))
% 3.50/3.71          | ((k2_relset_1 @ X41 @ X40 @ X42) = (X40))
% 3.50/3.71          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 3.50/3.71          | ~ (v1_funct_2 @ X42 @ X41 @ X40)
% 3.50/3.71          | ~ (v1_funct_1 @ X42))),
% 3.50/3.71      inference('demod', [status(thm)], ['34', '35'])).
% 3.50/3.71  thf('37', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 3.50/3.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 3.50/3.71          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 3.50/3.71          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 3.50/3.71               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 3.50/3.71               (k6_relat_1 @ sk_A_1))
% 3.50/3.71          | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 3.50/3.71          | ~ (v1_funct_1 @ sk_C))),
% 3.50/3.71      inference('sup-', [status(thm)], ['33', '36'])).
% 3.50/3.71  thf('38', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('40', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 3.50/3.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 3.50/3.71          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 3.50/3.71          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 3.50/3.71               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 3.50/3.71               (k6_relat_1 @ sk_A_1)))),
% 3.50/3.71      inference('demod', [status(thm)], ['37', '38', '39'])).
% 3.50/3.71  thf('41', plain,
% 3.50/3.71      ((~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.50/3.71           (k6_relat_1 @ sk_A_1))
% 3.50/3.71        | ((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (sk_A_1))
% 3.50/3.71        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 3.50/3.71        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 3.50/3.71        | ~ (v1_funct_1 @ sk_D))),
% 3.50/3.71      inference('sup-', [status(thm)], ['32', '40'])).
% 3.50/3.71  thf('42', plain,
% 3.50/3.71      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.50/3.71        (k6_relat_1 @ sk_A_1))),
% 3.50/3.71      inference('demod', [status(thm)], ['2', '11'])).
% 3.50/3.71  thf('43', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf(redefinition_k2_relset_1, axiom,
% 3.50/3.71    (![A:$i,B:$i,C:$i]:
% 3.50/3.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.50/3.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.50/3.71  thf('44', plain,
% 3.50/3.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.50/3.71         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 3.50/3.71          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.50/3.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.50/3.71  thf('45', plain,
% 3.50/3.71      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.50/3.71      inference('sup-', [status(thm)], ['43', '44'])).
% 3.50/3.71  thf('46', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('47', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('49', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 3.50/3.71      inference('demod', [status(thm)], ['41', '42', '45', '46', '47', '48'])).
% 3.50/3.71  thf('50', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf(cc1_relset_1, axiom,
% 3.50/3.71    (![A:$i,B:$i,C:$i]:
% 3.50/3.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.50/3.71       ( v1_relat_1 @ C ) ))).
% 3.50/3.71  thf('51', plain,
% 3.50/3.71      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.50/3.71         ((v1_relat_1 @ X14)
% 3.50/3.71          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.50/3.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.50/3.71  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 3.50/3.71      inference('sup-', [status(thm)], ['50', '51'])).
% 3.50/3.71  thf('53', plain, ((v1_funct_1 @ sk_D)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('54', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('55', plain,
% 3.50/3.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.50/3.71         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 3.50/3.71          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.50/3.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.50/3.71  thf('56', plain,
% 3.50/3.71      (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.50/3.71      inference('sup-', [status(thm)], ['54', '55'])).
% 3.50/3.71  thf('57', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('58', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.50/3.71      inference('sup+', [status(thm)], ['56', '57'])).
% 3.50/3.71  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('60', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('61', plain,
% 3.50/3.71      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.50/3.71         ((v1_relat_1 @ X14)
% 3.50/3.71          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.50/3.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.50/3.71  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 3.50/3.71      inference('sup-', [status(thm)], ['60', '61'])).
% 3.50/3.71  thf('63', plain,
% 3.50/3.71      ((((k6_relat_1 @ sk_A_1) != (k6_relat_1 @ sk_A_1))
% 3.50/3.71        | ~ (v2_funct_1 @ sk_D)
% 3.50/3.71        | ((sk_B) != (k1_relat_1 @ sk_D))
% 3.50/3.71        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 3.50/3.71      inference('demod', [status(thm)],
% 3.50/3.71                ['31', '49', '52', '53', '58', '59', '62'])).
% 3.50/3.71  thf('64', plain,
% 3.50/3.71      ((((sk_C) = (k2_funct_1 @ sk_D))
% 3.50/3.71        | ((sk_B) != (k1_relat_1 @ sk_D))
% 3.50/3.71        | ~ (v2_funct_1 @ sk_D))),
% 3.50/3.71      inference('simplify', [status(thm)], ['63'])).
% 3.50/3.71  thf('65', plain,
% 3.50/3.71      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 3.50/3.71         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.50/3.71      inference('demod', [status(thm)], ['9', '10'])).
% 3.50/3.71  thf('66', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A_1))),
% 3.50/3.71      inference('demod', [status(thm)], ['25', '28'])).
% 3.50/3.71  thf('67', plain,
% 3.50/3.71      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 3.50/3.71         = (k6_relat_1 @ sk_A_1))),
% 3.50/3.71      inference('demod', [status(thm)], ['65', '66'])).
% 3.50/3.71  thf('68', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf(t30_funct_2, axiom,
% 3.50/3.71    (![A:$i,B:$i,C:$i,D:$i]:
% 3.50/3.71     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.50/3.71         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 3.50/3.71       ( ![E:$i]:
% 3.50/3.71         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 3.50/3.71             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 3.50/3.71           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 3.50/3.71               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 3.50/3.71             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 3.50/3.71               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 3.50/3.71  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 3.50/3.71  thf(zf_stmt_2, axiom,
% 3.50/3.71    (![C:$i,B:$i]:
% 3.50/3.71     ( ( zip_tseitin_1 @ C @ B ) =>
% 3.50/3.71       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 3.50/3.71  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 3.50/3.71  thf(zf_stmt_4, axiom,
% 3.50/3.71    (![E:$i,D:$i]:
% 3.50/3.71     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 3.50/3.71  thf(zf_stmt_5, axiom,
% 3.50/3.71    (![A:$i,B:$i,C:$i,D:$i]:
% 3.50/3.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.50/3.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.50/3.71       ( ![E:$i]:
% 3.50/3.71         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.50/3.71             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.50/3.71           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 3.50/3.71               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 3.50/3.71             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 3.50/3.71  thf('69', plain,
% 3.50/3.71      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 3.50/3.71         (~ (v1_funct_1 @ X47)
% 3.50/3.71          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 3.50/3.71          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 3.50/3.71          | (zip_tseitin_0 @ X47 @ X50)
% 3.50/3.71          | ~ (v2_funct_1 @ (k1_partfun1 @ X51 @ X48 @ X48 @ X49 @ X50 @ X47))
% 3.50/3.71          | (zip_tseitin_1 @ X49 @ X48)
% 3.50/3.71          | ((k2_relset_1 @ X51 @ X48 @ X50) != (X48))
% 3.50/3.71          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X48)))
% 3.50/3.71          | ~ (v1_funct_2 @ X50 @ X51 @ X48)
% 3.50/3.71          | ~ (v1_funct_1 @ X50))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.50/3.71  thf('70', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         (~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.50/3.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.50/3.71          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 3.50/3.71          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 3.50/3.71          | ~ (v2_funct_1 @ 
% 3.50/3.71               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 3.50/3.71          | (zip_tseitin_0 @ sk_D @ X0)
% 3.50/3.71          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 3.50/3.71          | ~ (v1_funct_1 @ sk_D))),
% 3.50/3.71      inference('sup-', [status(thm)], ['68', '69'])).
% 3.50/3.71  thf('71', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('73', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         (~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.50/3.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.50/3.71          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 3.50/3.71          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 3.50/3.71          | ~ (v2_funct_1 @ 
% 3.50/3.71               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 3.50/3.71          | (zip_tseitin_0 @ sk_D @ X0))),
% 3.50/3.71      inference('demod', [status(thm)], ['70', '71', '72'])).
% 3.50/3.71  thf('74', plain,
% 3.50/3.71      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A_1))
% 3.50/3.71        | (zip_tseitin_0 @ sk_D @ sk_C)
% 3.50/3.71        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 3.50/3.71        | ((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 3.50/3.71        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 3.50/3.71        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 3.50/3.71        | ~ (v1_funct_1 @ sk_C))),
% 3.50/3.71      inference('sup-', [status(thm)], ['67', '73'])).
% 3.50/3.71  thf(fc4_funct_1, axiom,
% 3.50/3.71    (![A:$i]:
% 3.50/3.71     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.50/3.71       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.50/3.71  thf('75', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 3.50/3.71      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.50/3.71  thf('76', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('77', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('78', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('80', plain,
% 3.50/3.71      (((zip_tseitin_0 @ sk_D @ sk_C)
% 3.50/3.71        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 3.50/3.71        | ((sk_B) != (sk_B)))),
% 3.50/3.71      inference('demod', [status(thm)], ['74', '75', '76', '77', '78', '79'])).
% 3.50/3.71  thf('81', plain,
% 3.50/3.71      (((zip_tseitin_1 @ sk_A_1 @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 3.50/3.71      inference('simplify', [status(thm)], ['80'])).
% 3.50/3.71  thf('82', plain,
% 3.50/3.71      (![X45 : $i, X46 : $i]:
% 3.50/3.71         (((X45) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X45 @ X46))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.50/3.71  thf('83', plain,
% 3.50/3.71      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A_1) = (k1_xboole_0)))),
% 3.50/3.71      inference('sup-', [status(thm)], ['81', '82'])).
% 3.50/3.71  thf('84', plain, (((sk_A_1) != (k1_xboole_0))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('85', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 3.50/3.71      inference('simplify_reflect-', [status(thm)], ['83', '84'])).
% 3.50/3.71  thf('86', plain,
% 3.50/3.71      (![X43 : $i, X44 : $i]:
% 3.50/3.71         ((v2_funct_1 @ X44) | ~ (zip_tseitin_0 @ X44 @ X43))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.50/3.71  thf('87', plain, ((v2_funct_1 @ sk_D)),
% 3.50/3.71      inference('sup-', [status(thm)], ['85', '86'])).
% 3.50/3.71  thf('88', plain,
% 3.50/3.71      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 3.50/3.71      inference('demod', [status(thm)], ['64', '87'])).
% 3.50/3.71  thf('89', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf(t35_funct_2, axiom,
% 3.50/3.71    (![A:$i,B:$i,C:$i]:
% 3.50/3.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.50/3.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.50/3.71       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 3.50/3.71         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.50/3.71           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 3.50/3.71             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 3.50/3.71  thf('90', plain,
% 3.50/3.71      (![X52 : $i, X53 : $i, X54 : $i]:
% 3.50/3.71         (((X52) = (k1_xboole_0))
% 3.50/3.71          | ~ (v1_funct_1 @ X53)
% 3.50/3.71          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 3.50/3.71          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 3.50/3.71          | ((k5_relat_1 @ X53 @ (k2_funct_1 @ X53)) = (k6_partfun1 @ X54))
% 3.50/3.71          | ~ (v2_funct_1 @ X53)
% 3.50/3.71          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 3.50/3.71      inference('cnf', [status(esa)], [t35_funct_2])).
% 3.50/3.71  thf('91', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 3.50/3.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.50/3.71  thf('92', plain,
% 3.50/3.71      (![X52 : $i, X53 : $i, X54 : $i]:
% 3.50/3.71         (((X52) = (k1_xboole_0))
% 3.50/3.71          | ~ (v1_funct_1 @ X53)
% 3.50/3.71          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 3.50/3.71          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 3.50/3.71          | ((k5_relat_1 @ X53 @ (k2_funct_1 @ X53)) = (k6_relat_1 @ X54))
% 3.50/3.71          | ~ (v2_funct_1 @ X53)
% 3.50/3.71          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 3.50/3.71      inference('demod', [status(thm)], ['90', '91'])).
% 3.50/3.71  thf('93', plain,
% 3.50/3.71      ((((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) != (sk_A_1))
% 3.50/3.71        | ~ (v2_funct_1 @ sk_D)
% 3.50/3.71        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 3.50/3.71        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 3.50/3.71        | ~ (v1_funct_1 @ sk_D)
% 3.50/3.71        | ((sk_A_1) = (k1_xboole_0)))),
% 3.50/3.71      inference('sup-', [status(thm)], ['89', '92'])).
% 3.50/3.71  thf('94', plain,
% 3.50/3.71      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.50/3.71      inference('sup-', [status(thm)], ['43', '44'])).
% 3.50/3.71  thf('95', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('96', plain, ((v1_funct_1 @ sk_D)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('97', plain,
% 3.50/3.71      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 3.50/3.71        | ~ (v2_funct_1 @ sk_D)
% 3.50/3.71        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 3.50/3.71        | ((sk_A_1) = (k1_xboole_0)))),
% 3.50/3.71      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 3.50/3.71  thf('98', plain, (((sk_A_1) != (k1_xboole_0))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('99', plain,
% 3.50/3.71      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 3.50/3.71        | ~ (v2_funct_1 @ sk_D)
% 3.50/3.71        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 3.50/3.71      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 3.50/3.71  thf('100', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 3.50/3.71      inference('demod', [status(thm)], ['41', '42', '45', '46', '47', '48'])).
% 3.50/3.71  thf('101', plain,
% 3.50/3.71      ((((sk_A_1) != (sk_A_1))
% 3.50/3.71        | ~ (v2_funct_1 @ sk_D)
% 3.50/3.71        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 3.50/3.71      inference('demod', [status(thm)], ['99', '100'])).
% 3.50/3.71  thf('102', plain,
% 3.50/3.71      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 3.50/3.71        | ~ (v2_funct_1 @ sk_D))),
% 3.50/3.71      inference('simplify', [status(thm)], ['101'])).
% 3.50/3.71  thf('103', plain, ((v2_funct_1 @ sk_D)),
% 3.50/3.71      inference('sup-', [status(thm)], ['85', '86'])).
% 3.50/3.71  thf('104', plain,
% 3.50/3.71      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 3.50/3.71      inference('demod', [status(thm)], ['102', '103'])).
% 3.50/3.71  thf(t65_funct_1, axiom,
% 3.50/3.71    (![A:$i]:
% 3.50/3.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.50/3.71       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 3.50/3.71  thf('105', plain,
% 3.50/3.71      (![X13 : $i]:
% 3.50/3.71         (~ (v2_funct_1 @ X13)
% 3.50/3.71          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.50/3.71          | ~ (v1_funct_1 @ X13)
% 3.50/3.71          | ~ (v1_relat_1 @ X13))),
% 3.50/3.71      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.50/3.71  thf(fc6_funct_1, axiom,
% 3.50/3.71    (![A:$i]:
% 3.50/3.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 3.50/3.71       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.50/3.71         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 3.50/3.71         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.50/3.71  thf('106', plain,
% 3.50/3.71      (![X8 : $i]:
% 3.50/3.71         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 3.50/3.71          | ~ (v2_funct_1 @ X8)
% 3.50/3.71          | ~ (v1_funct_1 @ X8)
% 3.50/3.71          | ~ (v1_relat_1 @ X8))),
% 3.50/3.71      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.50/3.71  thf(dt_k2_funct_1, axiom,
% 3.50/3.71    (![A:$i]:
% 3.50/3.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.50/3.71       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.50/3.71         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.50/3.71  thf('107', plain,
% 3.50/3.71      (![X5 : $i]:
% 3.50/3.71         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 3.50/3.71          | ~ (v1_funct_1 @ X5)
% 3.50/3.71          | ~ (v1_relat_1 @ X5))),
% 3.50/3.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.50/3.71  thf('108', plain,
% 3.50/3.71      (![X5 : $i]:
% 3.50/3.71         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 3.50/3.71          | ~ (v1_funct_1 @ X5)
% 3.50/3.71          | ~ (v1_relat_1 @ X5))),
% 3.50/3.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.50/3.71  thf('109', plain,
% 3.50/3.71      (![X13 : $i]:
% 3.50/3.71         (~ (v2_funct_1 @ X13)
% 3.50/3.71          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.50/3.71          | ~ (v1_funct_1 @ X13)
% 3.50/3.71          | ~ (v1_relat_1 @ X13))),
% 3.50/3.71      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.50/3.71  thf('110', plain,
% 3.50/3.71      (![X8 : $i]:
% 3.50/3.71         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 3.50/3.71          | ~ (v2_funct_1 @ X8)
% 3.50/3.71          | ~ (v1_funct_1 @ X8)
% 3.50/3.71          | ~ (v1_relat_1 @ X8))),
% 3.50/3.71      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.50/3.71  thf('111', plain,
% 3.50/3.71      (![X5 : $i]:
% 3.50/3.71         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 3.50/3.71          | ~ (v1_funct_1 @ X5)
% 3.50/3.71          | ~ (v1_relat_1 @ X5))),
% 3.50/3.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.50/3.71  thf('112', plain,
% 3.50/3.71      (![X5 : $i]:
% 3.50/3.71         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 3.50/3.71          | ~ (v1_funct_1 @ X5)
% 3.50/3.71          | ~ (v1_relat_1 @ X5))),
% 3.50/3.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.50/3.71  thf('113', plain,
% 3.50/3.71      (![X13 : $i]:
% 3.50/3.71         (~ (v2_funct_1 @ X13)
% 3.50/3.71          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.50/3.71          | ~ (v1_funct_1 @ X13)
% 3.50/3.71          | ~ (v1_relat_1 @ X13))),
% 3.50/3.71      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.50/3.71  thf('114', plain,
% 3.50/3.71      (![X8 : $i]:
% 3.50/3.71         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 3.50/3.71          | ~ (v2_funct_1 @ X8)
% 3.50/3.71          | ~ (v1_funct_1 @ X8)
% 3.50/3.71          | ~ (v1_relat_1 @ X8))),
% 3.50/3.71      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.50/3.71  thf('115', plain,
% 3.50/3.71      (![X5 : $i]:
% 3.50/3.71         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 3.50/3.71          | ~ (v1_funct_1 @ X5)
% 3.50/3.71          | ~ (v1_relat_1 @ X5))),
% 3.50/3.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.50/3.71  thf('116', plain,
% 3.50/3.71      (![X5 : $i]:
% 3.50/3.71         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 3.50/3.71          | ~ (v1_funct_1 @ X5)
% 3.50/3.71          | ~ (v1_relat_1 @ X5))),
% 3.50/3.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.50/3.71  thf('117', plain,
% 3.50/3.71      (![X13 : $i]:
% 3.50/3.71         (~ (v2_funct_1 @ X13)
% 3.50/3.71          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.50/3.71          | ~ (v1_funct_1 @ X13)
% 3.50/3.71          | ~ (v1_relat_1 @ X13))),
% 3.50/3.71      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.50/3.71  thf(t59_funct_1, axiom,
% 3.50/3.71    (![A:$i]:
% 3.50/3.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.50/3.71       ( ( v2_funct_1 @ A ) =>
% 3.50/3.71         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 3.50/3.71             ( k2_relat_1 @ A ) ) & 
% 3.50/3.71           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 3.50/3.71             ( k2_relat_1 @ A ) ) ) ) ))).
% 3.50/3.71  thf('118', plain,
% 3.50/3.71      (![X10 : $i]:
% 3.50/3.71         (~ (v2_funct_1 @ X10)
% 3.50/3.71          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X10) @ X10))
% 3.50/3.71              = (k2_relat_1 @ X10))
% 3.50/3.71          | ~ (v1_funct_1 @ X10)
% 3.50/3.71          | ~ (v1_relat_1 @ X10))),
% 3.50/3.71      inference('cnf', [status(esa)], [t59_funct_1])).
% 3.50/3.71  thf('119', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.50/3.71      inference('sup+', [status(thm)], ['117', '118'])).
% 3.50/3.71  thf('120', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['116', '119'])).
% 3.50/3.71  thf('121', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['120'])).
% 3.50/3.71  thf('122', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['115', '121'])).
% 3.50/3.71  thf('123', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['122'])).
% 3.50/3.71  thf('124', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['114', '123'])).
% 3.50/3.71  thf('125', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['124'])).
% 3.50/3.71  thf('126', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.50/3.71      inference('sup+', [status(thm)], ['113', '125'])).
% 3.50/3.71  thf('127', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71              = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['112', '126'])).
% 3.50/3.71  thf('128', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['127'])).
% 3.50/3.71  thf('129', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71              = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['111', '128'])).
% 3.50/3.71  thf('130', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['129'])).
% 3.50/3.71  thf('131', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71              = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['110', '130'])).
% 3.50/3.71  thf('132', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['131'])).
% 3.50/3.71  thf('133', plain,
% 3.50/3.71      (![X8 : $i]:
% 3.50/3.71         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 3.50/3.71          | ~ (v2_funct_1 @ X8)
% 3.50/3.71          | ~ (v1_funct_1 @ X8)
% 3.50/3.71          | ~ (v1_relat_1 @ X8))),
% 3.50/3.71      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.50/3.71  thf('134', plain,
% 3.50/3.71      (![X5 : $i]:
% 3.50/3.71         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 3.50/3.71          | ~ (v1_funct_1 @ X5)
% 3.50/3.71          | ~ (v1_relat_1 @ X5))),
% 3.50/3.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.50/3.71  thf('135', plain,
% 3.50/3.71      (![X5 : $i]:
% 3.50/3.71         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 3.50/3.71          | ~ (v1_funct_1 @ X5)
% 3.50/3.71          | ~ (v1_relat_1 @ X5))),
% 3.50/3.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.50/3.71  thf('136', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['131'])).
% 3.50/3.71  thf(t55_funct_1, axiom,
% 3.50/3.71    (![A:$i]:
% 3.50/3.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.50/3.71       ( ( v2_funct_1 @ A ) =>
% 3.50/3.71         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.50/3.71           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.50/3.71  thf('137', plain,
% 3.50/3.71      (![X9 : $i]:
% 3.50/3.71         (~ (v2_funct_1 @ X9)
% 3.50/3.71          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 3.50/3.71          | ~ (v1_funct_1 @ X9)
% 3.50/3.71          | ~ (v1_relat_1 @ X9))),
% 3.50/3.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.50/3.71  thf('138', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 3.50/3.71            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.50/3.71      inference('sup+', [status(thm)], ['136', '137'])).
% 3.50/3.71  thf('139', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 3.50/3.71              = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['135', '138'])).
% 3.50/3.71  thf('140', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 3.50/3.71            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['139'])).
% 3.50/3.71  thf('141', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 3.50/3.71              = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['134', '140'])).
% 3.50/3.71  thf('142', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 3.50/3.71            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['141'])).
% 3.50/3.71  thf('143', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 3.50/3.71              = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['133', '142'])).
% 3.50/3.71  thf('144', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 3.50/3.71            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['143'])).
% 3.50/3.71  thf('145', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0))),
% 3.50/3.71      inference('sup+', [status(thm)], ['132', '144'])).
% 3.50/3.71  thf('146', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 3.50/3.71              = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.50/3.71      inference('simplify', [status(thm)], ['145'])).
% 3.50/3.71  thf('147', plain,
% 3.50/3.71      (![X8 : $i]:
% 3.50/3.71         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 3.50/3.71          | ~ (v2_funct_1 @ X8)
% 3.50/3.71          | ~ (v1_funct_1 @ X8)
% 3.50/3.71          | ~ (v1_relat_1 @ X8))),
% 3.50/3.71      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.50/3.71  thf('148', plain,
% 3.50/3.71      (![X5 : $i]:
% 3.50/3.71         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 3.50/3.71          | ~ (v1_funct_1 @ X5)
% 3.50/3.71          | ~ (v1_relat_1 @ X5))),
% 3.50/3.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.50/3.71  thf('149', plain,
% 3.50/3.71      (![X5 : $i]:
% 3.50/3.71         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 3.50/3.71          | ~ (v1_funct_1 @ X5)
% 3.50/3.71          | ~ (v1_relat_1 @ X5))),
% 3.50/3.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.50/3.71  thf('150', plain,
% 3.50/3.71      (![X13 : $i]:
% 3.50/3.71         (~ (v2_funct_1 @ X13)
% 3.50/3.71          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.50/3.71          | ~ (v1_funct_1 @ X13)
% 3.50/3.71          | ~ (v1_relat_1 @ X13))),
% 3.50/3.71      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.50/3.71  thf('151', plain,
% 3.50/3.71      (![X8 : $i]:
% 3.50/3.71         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 3.50/3.71          | ~ (v2_funct_1 @ X8)
% 3.50/3.71          | ~ (v1_funct_1 @ X8)
% 3.50/3.71          | ~ (v1_relat_1 @ X8))),
% 3.50/3.71      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.50/3.71  thf('152', plain,
% 3.50/3.71      (![X5 : $i]:
% 3.50/3.71         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 3.50/3.71          | ~ (v1_funct_1 @ X5)
% 3.50/3.71          | ~ (v1_relat_1 @ X5))),
% 3.50/3.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.50/3.71  thf('153', plain,
% 3.50/3.71      (![X5 : $i]:
% 3.50/3.71         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 3.50/3.71          | ~ (v1_funct_1 @ X5)
% 3.50/3.71          | ~ (v1_relat_1 @ X5))),
% 3.50/3.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.50/3.71  thf('154', plain,
% 3.50/3.71      (![X13 : $i]:
% 3.50/3.71         (~ (v2_funct_1 @ X13)
% 3.50/3.71          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.50/3.71          | ~ (v1_funct_1 @ X13)
% 3.50/3.71          | ~ (v1_relat_1 @ X13))),
% 3.50/3.71      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.50/3.71  thf('155', plain,
% 3.50/3.71      (![X10 : $i]:
% 3.50/3.71         (~ (v2_funct_1 @ X10)
% 3.50/3.71          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X10) @ X10))
% 3.50/3.71              = (k2_relat_1 @ X10))
% 3.50/3.71          | ~ (v1_funct_1 @ X10)
% 3.50/3.71          | ~ (v1_relat_1 @ X10))),
% 3.50/3.71      inference('cnf', [status(esa)], [t59_funct_1])).
% 3.50/3.71  thf('156', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.50/3.71      inference('sup+', [status(thm)], ['154', '155'])).
% 3.50/3.71  thf('157', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['153', '156'])).
% 3.50/3.71  thf('158', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['157'])).
% 3.50/3.71  thf('159', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['152', '158'])).
% 3.50/3.71  thf('160', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['159'])).
% 3.50/3.71  thf('161', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['151', '160'])).
% 3.50/3.71  thf('162', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['161'])).
% 3.50/3.71  thf('163', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.50/3.71      inference('sup+', [status(thm)], ['150', '162'])).
% 3.50/3.71  thf('164', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71              = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['149', '163'])).
% 3.50/3.71  thf('165', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['164'])).
% 3.50/3.71  thf('166', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71              = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['148', '165'])).
% 3.50/3.71  thf('167', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['166'])).
% 3.50/3.71  thf('168', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71              = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['147', '167'])).
% 3.50/3.71  thf('169', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71            = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['168'])).
% 3.50/3.71  thf('170', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0))),
% 3.50/3.71      inference('sup+', [status(thm)], ['146', '169'])).
% 3.50/3.71  thf('171', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 3.50/3.71              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 3.50/3.71      inference('simplify', [status(thm)], ['170'])).
% 3.50/3.71  thf('172', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.50/3.71      inference('sup+', [status(thm)], ['109', '171'])).
% 3.50/3.71  thf('173', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['108', '172'])).
% 3.50/3.71  thf('174', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['173'])).
% 3.50/3.71  thf('175', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['107', '174'])).
% 3.50/3.71  thf('176', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['175'])).
% 3.50/3.71  thf('177', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['106', '176'])).
% 3.50/3.71  thf('178', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['177'])).
% 3.50/3.71  thf('179', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71            = (k1_relat_1 @ X0))
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v2_funct_1 @ X0))),
% 3.50/3.71      inference('sup+', [status(thm)], ['105', '178'])).
% 3.50/3.71  thf('180', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (~ (v2_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0)
% 3.50/3.71          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 3.50/3.71              = (k1_relat_1 @ X0)))),
% 3.50/3.71      inference('simplify', [status(thm)], ['179'])).
% 3.50/3.71  thf('181', plain,
% 3.50/3.71      ((((k1_relat_1 @ (k6_relat_1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 3.50/3.71        | ~ (v1_relat_1 @ sk_D)
% 3.50/3.71        | ~ (v1_funct_1 @ sk_D)
% 3.50/3.71        | ~ (v2_funct_1 @ sk_D))),
% 3.50/3.71      inference('sup+', [status(thm)], ['104', '180'])).
% 3.50/3.71  thf(t71_relat_1, axiom,
% 3.50/3.71    (![A:$i]:
% 3.50/3.71     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.50/3.71       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.50/3.71  thf('182', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 3.50/3.71      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.50/3.71  thf('183', plain, ((v1_relat_1 @ sk_D)),
% 3.50/3.71      inference('sup-', [status(thm)], ['50', '51'])).
% 3.50/3.71  thf('184', plain, ((v1_funct_1 @ sk_D)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('185', plain, ((v2_funct_1 @ sk_D)),
% 3.50/3.71      inference('sup-', [status(thm)], ['85', '86'])).
% 3.50/3.71  thf('186', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 3.50/3.71      inference('demod', [status(thm)], ['181', '182', '183', '184', '185'])).
% 3.50/3.71  thf('187', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 3.50/3.71      inference('demod', [status(thm)], ['88', '186'])).
% 3.50/3.71  thf('188', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 3.50/3.71      inference('simplify', [status(thm)], ['187'])).
% 3.50/3.71  thf('189', plain,
% 3.50/3.71      (![X13 : $i]:
% 3.50/3.71         (~ (v2_funct_1 @ X13)
% 3.50/3.71          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.50/3.71          | ~ (v1_funct_1 @ X13)
% 3.50/3.71          | ~ (v1_relat_1 @ X13))),
% 3.50/3.71      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.50/3.71  thf('190', plain,
% 3.50/3.71      ((((k2_funct_1 @ sk_C) = (sk_D))
% 3.50/3.71        | ~ (v1_relat_1 @ sk_D)
% 3.50/3.71        | ~ (v1_funct_1 @ sk_D)
% 3.50/3.71        | ~ (v2_funct_1 @ sk_D))),
% 3.50/3.71      inference('sup+', [status(thm)], ['188', '189'])).
% 3.50/3.71  thf('191', plain, ((v1_relat_1 @ sk_D)),
% 3.50/3.71      inference('sup-', [status(thm)], ['50', '51'])).
% 3.50/3.71  thf('192', plain, ((v1_funct_1 @ sk_D)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('193', plain, ((v2_funct_1 @ sk_D)),
% 3.50/3.71      inference('sup-', [status(thm)], ['85', '86'])).
% 3.50/3.71  thf('194', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 3.50/3.71      inference('demod', [status(thm)], ['190', '191', '192', '193'])).
% 3.50/3.71  thf('195', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('196', plain, ($false),
% 3.50/3.71      inference('simplify_reflect-', [status(thm)], ['194', '195'])).
% 3.50/3.71  
% 3.50/3.71  % SZS output end Refutation
% 3.50/3.71  
% 3.50/3.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
