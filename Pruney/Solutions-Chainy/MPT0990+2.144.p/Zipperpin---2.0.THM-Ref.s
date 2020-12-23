%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sOYlMY858Z

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:19 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 515 expanded)
%              Number of leaves         :   48 ( 175 expanded)
%              Depth                    :   17
%              Number of atoms          : 1502 (11622 expanded)
%              Number of equality atoms :   95 ( 781 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('4',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X4 ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('6',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('16',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('30',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('31',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('32',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['13','14','33'])).

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

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X10 @ X11 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X10 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('36',plain,
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
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( r2_relset_1 @ X46 @ X46 @ ( k1_partfun1 @ X46 @ X47 @ X47 @ X46 @ X45 @ X48 ) @ ( k6_partfun1 @ X46 ) )
      | ( ( k2_relset_1 @ X47 @ X46 @ X48 )
        = X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('40',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('41',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( r2_relset_1 @ X46 @ X46 @ ( k1_partfun1 @ X46 @ X47 @ X47 @ X46 @ X45 @ X48 ) @ ( k6_relat_1 @ X46 ) )
      | ( ( k2_relset_1 @ X47 @ X46 @ X48 )
        = X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('48',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('49',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['46','50','53','54','55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('62',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
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

thf('66',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('67',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('68',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('70',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('71',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('76',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('77',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['67','74','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','57','58','59','64','78','79','84'])).

thf('86',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('88',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('91',plain,
    ( ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['13','14','33'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('93',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('94',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('95',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('96',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('97',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['62','63'])).

thf('99',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['67','74','77'])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['82','83'])).

thf('102',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['94','95','96','97','98','99','100','101'])).

thf('103',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['91','103'])).

thf('105',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['102'])).

thf('106',plain,
    ( sk_C
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['86','104','105'])).

thf('107',plain,
    ( ( k4_relat_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['6','106'])).

thf('108',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['82','83'])).

thf('113',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','114'])).

thf('116',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['107','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sOYlMY858Z
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:57:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.16/1.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.16/1.35  % Solved by: fo/fo7.sh
% 1.16/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.16/1.35  % done 447 iterations in 0.898s
% 1.16/1.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.16/1.35  % SZS output start Refutation
% 1.16/1.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.16/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.16/1.35  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.16/1.35  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.16/1.35  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.16/1.35  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.16/1.35  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.16/1.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.16/1.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.16/1.35  thf(sk_C_type, type, sk_C: $i).
% 1.16/1.35  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.16/1.35  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.16/1.35  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.16/1.35  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.16/1.35  thf(sk_D_type, type, sk_D: $i).
% 1.16/1.35  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.16/1.35  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.16/1.35  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.16/1.35  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.16/1.35  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.16/1.35  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.16/1.35  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.16/1.35  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.16/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.16/1.35  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.16/1.35  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.16/1.35  thf(t36_funct_2, conjecture,
% 1.16/1.35    (![A:$i,B:$i,C:$i]:
% 1.16/1.35     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.16/1.35         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.16/1.35       ( ![D:$i]:
% 1.16/1.35         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.16/1.35             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.16/1.35           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.16/1.35               ( r2_relset_1 @
% 1.16/1.35                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.16/1.35                 ( k6_partfun1 @ A ) ) & 
% 1.16/1.35               ( v2_funct_1 @ C ) ) =>
% 1.16/1.35             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.16/1.35               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.16/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.16/1.35    (~( ![A:$i,B:$i,C:$i]:
% 1.16/1.35        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.16/1.35            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.16/1.35          ( ![D:$i]:
% 1.16/1.35            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.16/1.35                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.16/1.35              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.16/1.35                  ( r2_relset_1 @
% 1.16/1.35                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.16/1.35                    ( k6_partfun1 @ A ) ) & 
% 1.16/1.35                  ( v2_funct_1 @ C ) ) =>
% 1.16/1.35                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.16/1.35                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.16/1.35    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.16/1.35  thf('0', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(cc2_relat_1, axiom,
% 1.16/1.35    (![A:$i]:
% 1.16/1.35     ( ( v1_relat_1 @ A ) =>
% 1.16/1.35       ( ![B:$i]:
% 1.16/1.35         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.16/1.35  thf('1', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.16/1.35          | (v1_relat_1 @ X0)
% 1.16/1.35          | ~ (v1_relat_1 @ X1))),
% 1.16/1.35      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.16/1.35  thf('2', plain,
% 1.16/1.35      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.16/1.35      inference('sup-', [status(thm)], ['0', '1'])).
% 1.16/1.35  thf(fc6_relat_1, axiom,
% 1.16/1.35    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.16/1.35  thf('3', plain,
% 1.16/1.35      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.16/1.35      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.16/1.35  thf('4', plain, ((v1_relat_1 @ sk_D)),
% 1.16/1.35      inference('demod', [status(thm)], ['2', '3'])).
% 1.16/1.35  thf(involutiveness_k4_relat_1, axiom,
% 1.16/1.35    (![A:$i]:
% 1.16/1.35     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 1.16/1.35  thf('5', plain,
% 1.16/1.35      (![X4 : $i]:
% 1.16/1.35         (((k4_relat_1 @ (k4_relat_1 @ X4)) = (X4)) | ~ (v1_relat_1 @ X4))),
% 1.16/1.35      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 1.16/1.35  thf('6', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 1.16/1.35      inference('sup-', [status(thm)], ['4', '5'])).
% 1.16/1.35  thf('7', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('8', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(redefinition_k1_partfun1, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.16/1.35     ( ( ( v1_funct_1 @ E ) & 
% 1.16/1.35         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.16/1.35         ( v1_funct_1 @ F ) & 
% 1.16/1.35         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.16/1.35       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.16/1.35  thf('9', plain,
% 1.16/1.35      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.16/1.35         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.16/1.35          | ~ (v1_funct_1 @ X38)
% 1.16/1.35          | ~ (v1_funct_1 @ X41)
% 1.16/1.35          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.16/1.35          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 1.16/1.35              = (k5_relat_1 @ X38 @ X41)))),
% 1.16/1.35      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.16/1.35  thf('10', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.35         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.16/1.35            = (k5_relat_1 @ sk_C @ X0))
% 1.16/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.16/1.35          | ~ (v1_funct_1 @ X0)
% 1.16/1.35          | ~ (v1_funct_1 @ sk_C))),
% 1.16/1.35      inference('sup-', [status(thm)], ['8', '9'])).
% 1.16/1.35  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('12', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.35         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.16/1.35            = (k5_relat_1 @ sk_C @ X0))
% 1.16/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.16/1.35          | ~ (v1_funct_1 @ X0))),
% 1.16/1.35      inference('demod', [status(thm)], ['10', '11'])).
% 1.16/1.35  thf('13', plain,
% 1.16/1.35      ((~ (v1_funct_1 @ sk_D)
% 1.16/1.35        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.16/1.35            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['7', '12'])).
% 1.16/1.35  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('15', plain,
% 1.16/1.35      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.16/1.35        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.16/1.35        (k6_partfun1 @ sk_A))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(redefinition_k6_partfun1, axiom,
% 1.16/1.35    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.16/1.35  thf('16', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 1.16/1.35      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.16/1.35  thf('17', plain,
% 1.16/1.35      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.16/1.35        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.16/1.35        (k6_relat_1 @ sk_A))),
% 1.16/1.35      inference('demod', [status(thm)], ['15', '16'])).
% 1.16/1.35  thf('18', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('19', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(dt_k1_partfun1, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.16/1.35     ( ( ( v1_funct_1 @ E ) & 
% 1.16/1.35         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.16/1.35         ( v1_funct_1 @ F ) & 
% 1.16/1.35         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.16/1.35       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.16/1.35         ( m1_subset_1 @
% 1.16/1.35           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.16/1.35           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.16/1.35  thf('20', plain,
% 1.16/1.35      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.16/1.35         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.16/1.35          | ~ (v1_funct_1 @ X30)
% 1.16/1.35          | ~ (v1_funct_1 @ X33)
% 1.16/1.35          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.16/1.35          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 1.16/1.35             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 1.16/1.35      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.16/1.35  thf('21', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.35         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.16/1.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.16/1.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.16/1.35          | ~ (v1_funct_1 @ X1)
% 1.16/1.35          | ~ (v1_funct_1 @ sk_C))),
% 1.16/1.35      inference('sup-', [status(thm)], ['19', '20'])).
% 1.16/1.35  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('23', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.35         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.16/1.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.16/1.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.16/1.35          | ~ (v1_funct_1 @ X1))),
% 1.16/1.35      inference('demod', [status(thm)], ['21', '22'])).
% 1.16/1.35  thf('24', plain,
% 1.16/1.35      ((~ (v1_funct_1 @ sk_D)
% 1.16/1.35        | (m1_subset_1 @ 
% 1.16/1.35           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.16/1.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.16/1.35      inference('sup-', [status(thm)], ['18', '23'])).
% 1.16/1.35  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('26', plain,
% 1.16/1.35      ((m1_subset_1 @ 
% 1.16/1.35        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.16/1.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.16/1.35      inference('demod', [status(thm)], ['24', '25'])).
% 1.16/1.35  thf(redefinition_r2_relset_1, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i,D:$i]:
% 1.16/1.35     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.16/1.35         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.16/1.35       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.16/1.35  thf('27', plain,
% 1.16/1.35      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.16/1.35         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.16/1.35          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.16/1.35          | ((X18) = (X21))
% 1.16/1.35          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 1.16/1.35      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.16/1.35  thf('28', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.16/1.35             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.16/1.35          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.16/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.16/1.35      inference('sup-', [status(thm)], ['26', '27'])).
% 1.16/1.35  thf('29', plain,
% 1.16/1.35      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.16/1.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.16/1.35        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.16/1.35            = (k6_relat_1 @ sk_A)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['17', '28'])).
% 1.16/1.35  thf(dt_k6_partfun1, axiom,
% 1.16/1.35    (![A:$i]:
% 1.16/1.35     ( ( m1_subset_1 @
% 1.16/1.35         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.16/1.35       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.16/1.35  thf('30', plain,
% 1.16/1.35      (![X37 : $i]:
% 1.16/1.35         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 1.16/1.35          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 1.16/1.35      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.16/1.35  thf('31', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 1.16/1.35      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.16/1.35  thf('32', plain,
% 1.16/1.35      (![X37 : $i]:
% 1.16/1.35         (m1_subset_1 @ (k6_relat_1 @ X37) @ 
% 1.16/1.35          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 1.16/1.35      inference('demod', [status(thm)], ['30', '31'])).
% 1.16/1.35  thf('33', plain,
% 1.16/1.35      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.16/1.35         = (k6_relat_1 @ sk_A))),
% 1.16/1.35      inference('demod', [status(thm)], ['29', '32'])).
% 1.16/1.35  thf('34', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.16/1.35      inference('demod', [status(thm)], ['13', '14', '33'])).
% 1.16/1.35  thf(t64_funct_1, axiom,
% 1.16/1.35    (![A:$i]:
% 1.16/1.35     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.16/1.35       ( ![B:$i]:
% 1.16/1.35         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.16/1.35           ( ( ( v2_funct_1 @ A ) & 
% 1.16/1.35               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.16/1.35               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.16/1.35             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.16/1.35  thf('35', plain,
% 1.16/1.35      (![X10 : $i, X11 : $i]:
% 1.16/1.35         (~ (v1_relat_1 @ X10)
% 1.16/1.35          | ~ (v1_funct_1 @ X10)
% 1.16/1.35          | ((X10) = (k2_funct_1 @ X11))
% 1.16/1.35          | ((k5_relat_1 @ X10 @ X11) != (k6_relat_1 @ (k2_relat_1 @ X11)))
% 1.16/1.35          | ((k2_relat_1 @ X10) != (k1_relat_1 @ X11))
% 1.16/1.35          | ~ (v2_funct_1 @ X11)
% 1.16/1.35          | ~ (v1_funct_1 @ X11)
% 1.16/1.35          | ~ (v1_relat_1 @ X11))),
% 1.16/1.35      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.16/1.35  thf('36', plain,
% 1.16/1.35      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 1.16/1.35        | ~ (v1_relat_1 @ sk_D)
% 1.16/1.35        | ~ (v1_funct_1 @ sk_D)
% 1.16/1.35        | ~ (v2_funct_1 @ sk_D)
% 1.16/1.35        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.16/1.35        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.16/1.35        | ~ (v1_funct_1 @ sk_C)
% 1.16/1.35        | ~ (v1_relat_1 @ sk_C))),
% 1.16/1.35      inference('sup-', [status(thm)], ['34', '35'])).
% 1.16/1.35  thf('37', plain,
% 1.16/1.35      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.16/1.35         = (k6_relat_1 @ sk_A))),
% 1.16/1.35      inference('demod', [status(thm)], ['29', '32'])).
% 1.16/1.35  thf('38', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(t24_funct_2, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i]:
% 1.16/1.35     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.16/1.35         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.16/1.35       ( ![D:$i]:
% 1.16/1.35         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.16/1.35             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.16/1.35           ( ( r2_relset_1 @
% 1.16/1.35               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.16/1.35               ( k6_partfun1 @ B ) ) =>
% 1.16/1.35             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.16/1.35  thf('39', plain,
% 1.16/1.35      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.16/1.35         (~ (v1_funct_1 @ X45)
% 1.16/1.35          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 1.16/1.35          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 1.16/1.35          | ~ (r2_relset_1 @ X46 @ X46 @ 
% 1.16/1.35               (k1_partfun1 @ X46 @ X47 @ X47 @ X46 @ X45 @ X48) @ 
% 1.16/1.35               (k6_partfun1 @ X46))
% 1.16/1.35          | ((k2_relset_1 @ X47 @ X46 @ X48) = (X46))
% 1.16/1.35          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 1.16/1.35          | ~ (v1_funct_2 @ X48 @ X47 @ X46)
% 1.16/1.35          | ~ (v1_funct_1 @ X48))),
% 1.16/1.35      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.16/1.35  thf('40', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 1.16/1.35      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.16/1.35  thf('41', plain,
% 1.16/1.35      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.16/1.35         (~ (v1_funct_1 @ X45)
% 1.16/1.35          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 1.16/1.35          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 1.16/1.35          | ~ (r2_relset_1 @ X46 @ X46 @ 
% 1.16/1.35               (k1_partfun1 @ X46 @ X47 @ X47 @ X46 @ X45 @ X48) @ 
% 1.16/1.35               (k6_relat_1 @ X46))
% 1.16/1.35          | ((k2_relset_1 @ X47 @ X46 @ X48) = (X46))
% 1.16/1.35          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 1.16/1.35          | ~ (v1_funct_2 @ X48 @ X47 @ X46)
% 1.16/1.35          | ~ (v1_funct_1 @ X48))),
% 1.16/1.35      inference('demod', [status(thm)], ['39', '40'])).
% 1.16/1.35  thf('42', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         (~ (v1_funct_1 @ X0)
% 1.16/1.35          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.16/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.16/1.35          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.16/1.35          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.16/1.35               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.16/1.35               (k6_relat_1 @ sk_A))
% 1.16/1.35          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.16/1.35          | ~ (v1_funct_1 @ sk_C))),
% 1.16/1.35      inference('sup-', [status(thm)], ['38', '41'])).
% 1.16/1.35  thf('43', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('45', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         (~ (v1_funct_1 @ X0)
% 1.16/1.35          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.16/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.16/1.35          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.16/1.35          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.16/1.35               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.16/1.35               (k6_relat_1 @ sk_A)))),
% 1.16/1.35      inference('demod', [status(thm)], ['42', '43', '44'])).
% 1.16/1.35  thf('46', plain,
% 1.16/1.35      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.16/1.35           (k6_relat_1 @ sk_A))
% 1.16/1.35        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.16/1.35        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.16/1.35        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.16/1.35        | ~ (v1_funct_1 @ sk_D))),
% 1.16/1.35      inference('sup-', [status(thm)], ['37', '45'])).
% 1.16/1.35  thf('47', plain,
% 1.16/1.35      (![X37 : $i]:
% 1.16/1.35         (m1_subset_1 @ (k6_relat_1 @ X37) @ 
% 1.16/1.35          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 1.16/1.35      inference('demod', [status(thm)], ['30', '31'])).
% 1.16/1.35  thf('48', plain,
% 1.16/1.35      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.16/1.35         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.16/1.35          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.16/1.35          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 1.16/1.35          | ((X18) != (X21)))),
% 1.16/1.35      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.16/1.35  thf('49', plain,
% 1.16/1.35      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.16/1.35         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 1.16/1.35          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.16/1.35      inference('simplify', [status(thm)], ['48'])).
% 1.16/1.35  thf('50', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.16/1.35      inference('sup-', [status(thm)], ['47', '49'])).
% 1.16/1.35  thf('51', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(redefinition_k2_relset_1, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i]:
% 1.16/1.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.16/1.35       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.16/1.35  thf('52', plain,
% 1.16/1.35      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.16/1.35         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.16/1.35          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.16/1.35      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.16/1.35  thf('53', plain,
% 1.16/1.35      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.16/1.35      inference('sup-', [status(thm)], ['51', '52'])).
% 1.16/1.35  thf('54', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('55', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('57', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.16/1.35      inference('demod', [status(thm)], ['46', '50', '53', '54', '55', '56'])).
% 1.16/1.35  thf('58', plain, ((v1_relat_1 @ sk_D)),
% 1.16/1.35      inference('demod', [status(thm)], ['2', '3'])).
% 1.16/1.35  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('60', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('61', plain,
% 1.16/1.35      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.16/1.35         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.16/1.35          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.16/1.35      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.16/1.35  thf('62', plain,
% 1.16/1.35      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.16/1.35      inference('sup-', [status(thm)], ['60', '61'])).
% 1.16/1.35  thf('63', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('64', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.16/1.35      inference('sup+', [status(thm)], ['62', '63'])).
% 1.16/1.35  thf('65', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(d1_funct_2, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i]:
% 1.16/1.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.16/1.35       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.16/1.35           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.16/1.35             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.16/1.35         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.16/1.35           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.16/1.35             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.16/1.35  thf(zf_stmt_1, axiom,
% 1.16/1.35    (![C:$i,B:$i,A:$i]:
% 1.16/1.35     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.16/1.35       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.16/1.35  thf('66', plain,
% 1.16/1.35      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.16/1.35         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 1.16/1.35          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 1.16/1.35          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.16/1.35  thf('67', plain,
% 1.16/1.35      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 1.16/1.35        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['65', '66'])).
% 1.16/1.35  thf(zf_stmt_2, axiom,
% 1.16/1.35    (![B:$i,A:$i]:
% 1.16/1.35     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.16/1.35       ( zip_tseitin_0 @ B @ A ) ))).
% 1.16/1.35  thf('68', plain,
% 1.16/1.35      (![X22 : $i, X23 : $i]:
% 1.16/1.35         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.16/1.35  thf('69', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.16/1.35  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.16/1.35  thf(zf_stmt_5, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i]:
% 1.16/1.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.16/1.35       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.16/1.35         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.16/1.35           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.16/1.35             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.16/1.35  thf('70', plain,
% 1.16/1.35      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.16/1.35         (~ (zip_tseitin_0 @ X27 @ X28)
% 1.16/1.35          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 1.16/1.35          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.16/1.35  thf('71', plain,
% 1.16/1.35      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 1.16/1.35      inference('sup-', [status(thm)], ['69', '70'])).
% 1.16/1.35  thf('72', plain,
% 1.16/1.35      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 1.16/1.35      inference('sup-', [status(thm)], ['68', '71'])).
% 1.16/1.35  thf('73', plain, (((sk_A) != (k1_xboole_0))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('74', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 1.16/1.35      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 1.16/1.35  thf('75', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(redefinition_k1_relset_1, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i]:
% 1.16/1.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.16/1.35       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.16/1.35  thf('76', plain,
% 1.16/1.35      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.16/1.35         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 1.16/1.35          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.16/1.35      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.16/1.35  thf('77', plain,
% 1.16/1.35      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.16/1.35      inference('sup-', [status(thm)], ['75', '76'])).
% 1.16/1.35  thf('78', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.16/1.35      inference('demod', [status(thm)], ['67', '74', '77'])).
% 1.16/1.35  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('80', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('81', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.16/1.35          | (v1_relat_1 @ X0)
% 1.16/1.35          | ~ (v1_relat_1 @ X1))),
% 1.16/1.35      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.16/1.35  thf('82', plain,
% 1.16/1.35      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.16/1.35      inference('sup-', [status(thm)], ['80', '81'])).
% 1.16/1.35  thf('83', plain,
% 1.16/1.35      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.16/1.35      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.16/1.35  thf('84', plain, ((v1_relat_1 @ sk_C)),
% 1.16/1.35      inference('demod', [status(thm)], ['82', '83'])).
% 1.16/1.35  thf('85', plain,
% 1.16/1.35      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 1.16/1.35        | ~ (v2_funct_1 @ sk_D)
% 1.16/1.35        | ((sk_B) != (sk_B))
% 1.16/1.35        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.16/1.35      inference('demod', [status(thm)],
% 1.16/1.35                ['36', '57', '58', '59', '64', '78', '79', '84'])).
% 1.16/1.35  thf('86', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.16/1.35      inference('simplify', [status(thm)], ['85'])).
% 1.16/1.35  thf('87', plain, ((v1_funct_1 @ sk_D)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(d9_funct_1, axiom,
% 1.16/1.35    (![A:$i]:
% 1.16/1.35     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.16/1.35       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.16/1.35  thf('88', plain,
% 1.16/1.35      (![X5 : $i]:
% 1.16/1.35         (~ (v2_funct_1 @ X5)
% 1.16/1.35          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 1.16/1.35          | ~ (v1_funct_1 @ X5)
% 1.16/1.35          | ~ (v1_relat_1 @ X5))),
% 1.16/1.35      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.16/1.35  thf('89', plain,
% 1.16/1.35      ((~ (v1_relat_1 @ sk_D)
% 1.16/1.35        | ((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))
% 1.16/1.35        | ~ (v2_funct_1 @ sk_D))),
% 1.16/1.35      inference('sup-', [status(thm)], ['87', '88'])).
% 1.16/1.35  thf('90', plain, ((v1_relat_1 @ sk_D)),
% 1.16/1.35      inference('demod', [status(thm)], ['2', '3'])).
% 1.16/1.35  thf('91', plain,
% 1.16/1.35      ((((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.16/1.35      inference('demod', [status(thm)], ['89', '90'])).
% 1.16/1.35  thf('92', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.16/1.35      inference('demod', [status(thm)], ['13', '14', '33'])).
% 1.16/1.35  thf(t48_funct_1, axiom,
% 1.16/1.35    (![A:$i]:
% 1.16/1.35     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.16/1.35       ( ![B:$i]:
% 1.16/1.35         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.16/1.35           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.16/1.35               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.16/1.35             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.16/1.35  thf('93', plain,
% 1.16/1.35      (![X8 : $i, X9 : $i]:
% 1.16/1.35         (~ (v1_relat_1 @ X8)
% 1.16/1.35          | ~ (v1_funct_1 @ X8)
% 1.16/1.35          | (v2_funct_1 @ X9)
% 1.16/1.35          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 1.16/1.35          | ~ (v2_funct_1 @ (k5_relat_1 @ X8 @ X9))
% 1.16/1.35          | ~ (v1_funct_1 @ X9)
% 1.16/1.35          | ~ (v1_relat_1 @ X9))),
% 1.16/1.35      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.16/1.35  thf('94', plain,
% 1.16/1.35      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.16/1.35        | ~ (v1_relat_1 @ sk_D)
% 1.16/1.35        | ~ (v1_funct_1 @ sk_D)
% 1.16/1.35        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.16/1.35        | (v2_funct_1 @ sk_D)
% 1.16/1.35        | ~ (v1_funct_1 @ sk_C)
% 1.16/1.35        | ~ (v1_relat_1 @ sk_C))),
% 1.16/1.35      inference('sup-', [status(thm)], ['92', '93'])).
% 1.16/1.35  thf(fc4_funct_1, axiom,
% 1.16/1.35    (![A:$i]:
% 1.16/1.35     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.16/1.35       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.16/1.35  thf('95', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 1.16/1.35      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.16/1.35  thf('96', plain, ((v1_relat_1 @ sk_D)),
% 1.16/1.35      inference('demod', [status(thm)], ['2', '3'])).
% 1.16/1.35  thf('97', plain, ((v1_funct_1 @ sk_D)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('98', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.16/1.35      inference('sup+', [status(thm)], ['62', '63'])).
% 1.16/1.35  thf('99', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.16/1.35      inference('demod', [status(thm)], ['67', '74', '77'])).
% 1.16/1.35  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 1.16/1.35      inference('demod', [status(thm)], ['82', '83'])).
% 1.16/1.35  thf('102', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 1.16/1.35      inference('demod', [status(thm)],
% 1.16/1.35                ['94', '95', '96', '97', '98', '99', '100', '101'])).
% 1.16/1.35  thf('103', plain, ((v2_funct_1 @ sk_D)),
% 1.16/1.35      inference('simplify', [status(thm)], ['102'])).
% 1.16/1.35  thf('104', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 1.16/1.35      inference('demod', [status(thm)], ['91', '103'])).
% 1.16/1.35  thf('105', plain, ((v2_funct_1 @ sk_D)),
% 1.16/1.35      inference('simplify', [status(thm)], ['102'])).
% 1.16/1.35  thf('106', plain, (((sk_C) = (k4_relat_1 @ sk_D))),
% 1.16/1.35      inference('demod', [status(thm)], ['86', '104', '105'])).
% 1.16/1.35  thf('107', plain, (((k4_relat_1 @ sk_C) = (sk_D))),
% 1.16/1.35      inference('demod', [status(thm)], ['6', '106'])).
% 1.16/1.35  thf('108', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('110', plain,
% 1.16/1.35      (![X5 : $i]:
% 1.16/1.35         (~ (v2_funct_1 @ X5)
% 1.16/1.35          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 1.16/1.35          | ~ (v1_funct_1 @ X5)
% 1.16/1.35          | ~ (v1_relat_1 @ X5))),
% 1.16/1.35      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.16/1.35  thf('111', plain,
% 1.16/1.35      ((~ (v1_relat_1 @ sk_C)
% 1.16/1.35        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 1.16/1.35        | ~ (v2_funct_1 @ sk_C))),
% 1.16/1.35      inference('sup-', [status(thm)], ['109', '110'])).
% 1.16/1.35  thf('112', plain, ((v1_relat_1 @ sk_C)),
% 1.16/1.35      inference('demod', [status(thm)], ['82', '83'])).
% 1.16/1.35  thf('113', plain, ((v2_funct_1 @ sk_C)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('114', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.16/1.35      inference('demod', [status(thm)], ['111', '112', '113'])).
% 1.16/1.35  thf('115', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 1.16/1.35      inference('demod', [status(thm)], ['108', '114'])).
% 1.16/1.35  thf('116', plain, ($false),
% 1.16/1.35      inference('simplify_reflect-', [status(thm)], ['107', '115'])).
% 1.16/1.35  
% 1.16/1.35  % SZS output end Refutation
% 1.16/1.35  
% 1.16/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
