%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JmlIwdqOqX

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:18 EST 2020

% Result     : Theorem 2.32s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  229 (1436 expanded)
%              Number of leaves         :   49 ( 430 expanded)
%              Depth                    :   27
%              Number of atoms          : 2312 (38041 expanded)
%              Number of equality atoms :  165 (2539 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
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
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','7','8','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 )
        = ( k5_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('26',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('37',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('41',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('42',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('43',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','44'])).

thf('46',plain,(
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

thf('47',plain,(
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

thf('48',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('49',plain,(
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
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['45','53'])).

thf('55',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('57',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['54','58','59','60','61','62'])).

thf('64',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','63'])).

thf('65',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','44'])).

thf('67',plain,(
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

thf('68',plain,(
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

thf('69',plain,(
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
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('74',plain,(
    ! [X13: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('75',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['73','74','75','76','77','78'])).

thf('80',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('82',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X43: $i,X44: $i] :
      ( ( v2_funct_1 @ X44 )
      | ~ ( zip_tseitin_0 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('86',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['65','86'])).

thf('88',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['40','43'])).

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

thf('89',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X15
        = ( k2_funct_1 @ X16 ) )
      | ( ( k5_relat_1 @ X15 @ X16 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
      | ( ( k2_relat_1 @ X15 )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('90',plain,
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
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('92',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('94',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('99',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('107',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['90','95','96','101','102','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['54','58','59','60','61','62'])).

thf('110',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('113',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['65','86'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('115',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('117',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['116'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('118',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('119',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['114','124'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('126',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('127',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('128',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('130',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['125','126','127','128','129'])).

thf('131',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['113','130'])).

thf('132',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['87','132'])).

thf('134',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X15
        = ( k2_funct_1 @ X16 ) )
      | ( ( k5_relat_1 @ X15 @ X16 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
      | ( ( k2_relat_1 @ X15 )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('135',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['99','100'])).

thf('137',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['105','106'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['54','58','59','60','61','62'])).

thf('141',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['99','100'])).

thf('143',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('144',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['99','100'])).

thf('145',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['105','106'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['143','148'])).

thf('150',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['142','149'])).

thf('151',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('152',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['105','106'])).

thf('155',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['150','151','152','153','154'])).

thf('156',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['141','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['105','106'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
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
    inference(demod,[status(thm)],['1','2'])).

thf('162',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['162','163','164','165','166'])).

thf('168',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('172',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['159','170','171'])).

thf('173',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('175',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['135','136','137','138','139','140','172','173','174'])).

thf('176',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['176','177'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JmlIwdqOqX
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.32/2.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.32/2.57  % Solved by: fo/fo7.sh
% 2.32/2.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.32/2.57  % done 1755 iterations in 2.116s
% 2.32/2.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.32/2.57  % SZS output start Refutation
% 2.32/2.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.32/2.57  thf(sk_B_type, type, sk_B: $i).
% 2.32/2.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.32/2.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.32/2.57  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.32/2.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.32/2.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.32/2.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.32/2.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.32/2.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.32/2.57  thf(sk_D_type, type, sk_D: $i).
% 2.32/2.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.32/2.57  thf(sk_C_type, type, sk_C: $i).
% 2.32/2.57  thf(sk_A_type, type, sk_A: $i).
% 2.32/2.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 2.32/2.57  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.32/2.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.32/2.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.32/2.57  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.32/2.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.32/2.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.32/2.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.32/2.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.32/2.57  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.32/2.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.32/2.57  thf(t36_funct_2, conjecture,
% 2.32/2.57    (![A:$i,B:$i,C:$i]:
% 2.32/2.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.32/2.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.57       ( ![D:$i]:
% 2.32/2.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.32/2.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.32/2.57           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.32/2.57               ( r2_relset_1 @
% 2.32/2.57                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.32/2.57                 ( k6_partfun1 @ A ) ) & 
% 2.32/2.57               ( v2_funct_1 @ C ) ) =>
% 2.32/2.57             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.32/2.57               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.32/2.57  thf(zf_stmt_0, negated_conjecture,
% 2.32/2.57    (~( ![A:$i,B:$i,C:$i]:
% 2.32/2.57        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.32/2.57            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.57          ( ![D:$i]:
% 2.32/2.57            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.32/2.57                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.32/2.57              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.32/2.57                  ( r2_relset_1 @
% 2.32/2.57                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.32/2.57                    ( k6_partfun1 @ A ) ) & 
% 2.32/2.57                  ( v2_funct_1 @ C ) ) =>
% 2.32/2.57                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.32/2.57                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.32/2.57    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.32/2.58  thf('0', plain,
% 2.32/2.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf(t35_funct_2, axiom,
% 2.32/2.58    (![A:$i,B:$i,C:$i]:
% 2.32/2.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.32/2.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.58       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.32/2.58         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.32/2.58           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 2.32/2.58             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 2.32/2.58  thf('1', plain,
% 2.32/2.58      (![X52 : $i, X53 : $i, X54 : $i]:
% 2.32/2.58         (((X52) = (k1_xboole_0))
% 2.32/2.58          | ~ (v1_funct_1 @ X53)
% 2.32/2.58          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 2.32/2.58          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 2.32/2.58          | ((k5_relat_1 @ X53 @ (k2_funct_1 @ X53)) = (k6_partfun1 @ X54))
% 2.32/2.58          | ~ (v2_funct_1 @ X53)
% 2.32/2.58          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 2.32/2.58      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.32/2.58  thf(redefinition_k6_partfun1, axiom,
% 2.32/2.58    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.32/2.58  thf('2', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 2.32/2.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.32/2.58  thf('3', plain,
% 2.32/2.58      (![X52 : $i, X53 : $i, X54 : $i]:
% 2.32/2.58         (((X52) = (k1_xboole_0))
% 2.32/2.58          | ~ (v1_funct_1 @ X53)
% 2.32/2.58          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 2.32/2.58          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 2.32/2.58          | ((k5_relat_1 @ X53 @ (k2_funct_1 @ X53)) = (k6_relat_1 @ X54))
% 2.32/2.58          | ~ (v2_funct_1 @ X53)
% 2.32/2.58          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 2.32/2.58      inference('demod', [status(thm)], ['1', '2'])).
% 2.32/2.58  thf('4', plain,
% 2.32/2.58      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 2.32/2.58        | ~ (v2_funct_1 @ sk_D)
% 2.32/2.58        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.32/2.58        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.32/2.58        | ~ (v1_funct_1 @ sk_D)
% 2.32/2.58        | ((sk_A) = (k1_xboole_0)))),
% 2.32/2.58      inference('sup-', [status(thm)], ['0', '3'])).
% 2.32/2.58  thf('5', plain,
% 2.32/2.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf(redefinition_k2_relset_1, axiom,
% 2.32/2.58    (![A:$i,B:$i,C:$i]:
% 2.32/2.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.32/2.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.32/2.58  thf('6', plain,
% 2.32/2.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.32/2.58         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 2.32/2.58          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 2.32/2.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.32/2.58  thf('7', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.32/2.58      inference('sup-', [status(thm)], ['5', '6'])).
% 2.32/2.58  thf('8', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('10', plain,
% 2.32/2.58      ((((k2_relat_1 @ sk_D) != (sk_A))
% 2.32/2.58        | ~ (v2_funct_1 @ sk_D)
% 2.32/2.58        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.32/2.58        | ((sk_A) = (k1_xboole_0)))),
% 2.32/2.58      inference('demod', [status(thm)], ['4', '7', '8', '9'])).
% 2.32/2.58  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('12', plain,
% 2.32/2.58      ((((k2_relat_1 @ sk_D) != (sk_A))
% 2.32/2.58        | ~ (v2_funct_1 @ sk_D)
% 2.32/2.58        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 2.32/2.58      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 2.32/2.58  thf('13', plain,
% 2.32/2.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('14', plain,
% 2.32/2.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf(redefinition_k1_partfun1, axiom,
% 2.32/2.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.32/2.58     ( ( ( v1_funct_1 @ E ) & 
% 2.32/2.58         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.32/2.58         ( v1_funct_1 @ F ) & 
% 2.32/2.58         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.32/2.58       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.32/2.58  thf('15', plain,
% 2.32/2.58      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 2.32/2.58         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 2.32/2.58          | ~ (v1_funct_1 @ X32)
% 2.32/2.58          | ~ (v1_funct_1 @ X35)
% 2.32/2.58          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 2.32/2.58          | ((k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 2.32/2.58              = (k5_relat_1 @ X32 @ X35)))),
% 2.32/2.58      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.32/2.58  thf('16', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.58         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.32/2.58            = (k5_relat_1 @ sk_C @ X0))
% 2.32/2.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.32/2.58          | ~ (v1_funct_1 @ X0)
% 2.32/2.58          | ~ (v1_funct_1 @ sk_C))),
% 2.32/2.58      inference('sup-', [status(thm)], ['14', '15'])).
% 2.32/2.58  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('18', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.58         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.32/2.58            = (k5_relat_1 @ sk_C @ X0))
% 2.32/2.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.32/2.58          | ~ (v1_funct_1 @ X0))),
% 2.32/2.58      inference('demod', [status(thm)], ['16', '17'])).
% 2.32/2.58  thf('19', plain,
% 2.32/2.58      ((~ (v1_funct_1 @ sk_D)
% 2.32/2.58        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.32/2.58            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.32/2.58      inference('sup-', [status(thm)], ['13', '18'])).
% 2.32/2.58  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('21', plain,
% 2.32/2.58      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.32/2.58         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.32/2.58      inference('demod', [status(thm)], ['19', '20'])).
% 2.32/2.58  thf('22', plain,
% 2.32/2.58      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.32/2.58        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.32/2.58        (k6_partfun1 @ sk_A))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('23', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 2.32/2.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.32/2.58  thf('24', plain,
% 2.32/2.58      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.32/2.58        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.32/2.58        (k6_relat_1 @ sk_A))),
% 2.32/2.58      inference('demod', [status(thm)], ['22', '23'])).
% 2.32/2.58  thf('25', plain,
% 2.32/2.58      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.32/2.58         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.32/2.58      inference('demod', [status(thm)], ['19', '20'])).
% 2.32/2.58  thf('26', plain,
% 2.32/2.58      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.32/2.58        (k6_relat_1 @ sk_A))),
% 2.32/2.58      inference('demod', [status(thm)], ['24', '25'])).
% 2.32/2.58  thf('27', plain,
% 2.32/2.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('28', plain,
% 2.32/2.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf(dt_k1_partfun1, axiom,
% 2.32/2.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.32/2.58     ( ( ( v1_funct_1 @ E ) & 
% 2.32/2.58         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.32/2.58         ( v1_funct_1 @ F ) & 
% 2.32/2.58         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.32/2.58       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.32/2.58         ( m1_subset_1 @
% 2.32/2.58           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.32/2.58           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.32/2.58  thf('29', plain,
% 2.32/2.58      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.32/2.58         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 2.32/2.58          | ~ (v1_funct_1 @ X24)
% 2.32/2.58          | ~ (v1_funct_1 @ X27)
% 2.32/2.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 2.32/2.58          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 2.32/2.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 2.32/2.58      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.32/2.58  thf('30', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.58         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.32/2.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.32/2.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.32/2.58          | ~ (v1_funct_1 @ X1)
% 2.32/2.58          | ~ (v1_funct_1 @ sk_C))),
% 2.32/2.58      inference('sup-', [status(thm)], ['28', '29'])).
% 2.32/2.58  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('32', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.58         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.32/2.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.32/2.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.32/2.58          | ~ (v1_funct_1 @ X1))),
% 2.32/2.58      inference('demod', [status(thm)], ['30', '31'])).
% 2.32/2.58  thf('33', plain,
% 2.32/2.58      ((~ (v1_funct_1 @ sk_D)
% 2.32/2.58        | (m1_subset_1 @ 
% 2.32/2.58           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.32/2.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.32/2.58      inference('sup-', [status(thm)], ['27', '32'])).
% 2.32/2.58  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('35', plain,
% 2.32/2.58      ((m1_subset_1 @ 
% 2.32/2.58        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.32/2.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.32/2.58      inference('demod', [status(thm)], ['33', '34'])).
% 2.32/2.58  thf('36', plain,
% 2.32/2.58      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.32/2.58         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.32/2.58      inference('demod', [status(thm)], ['19', '20'])).
% 2.32/2.58  thf('37', plain,
% 2.32/2.58      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.32/2.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.32/2.58      inference('demod', [status(thm)], ['35', '36'])).
% 2.32/2.58  thf(redefinition_r2_relset_1, axiom,
% 2.32/2.58    (![A:$i,B:$i,C:$i,D:$i]:
% 2.32/2.58     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.32/2.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.58       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.32/2.58  thf('38', plain,
% 2.32/2.58      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.32/2.58         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 2.32/2.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 2.32/2.58          | ((X20) = (X23))
% 2.32/2.58          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 2.32/2.58      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.32/2.58  thf('39', plain,
% 2.32/2.58      (![X0 : $i]:
% 2.32/2.58         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 2.32/2.58          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 2.32/2.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.32/2.58      inference('sup-', [status(thm)], ['37', '38'])).
% 2.32/2.58  thf('40', plain,
% 2.32/2.58      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.32/2.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.32/2.58        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 2.32/2.58      inference('sup-', [status(thm)], ['26', '39'])).
% 2.32/2.58  thf(dt_k6_partfun1, axiom,
% 2.32/2.58    (![A:$i]:
% 2.32/2.58     ( ( m1_subset_1 @
% 2.32/2.58         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.32/2.58       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.32/2.58  thf('41', plain,
% 2.32/2.58      (![X31 : $i]:
% 2.32/2.58         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 2.32/2.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 2.32/2.58      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.32/2.58  thf('42', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 2.32/2.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.32/2.58  thf('43', plain,
% 2.32/2.58      (![X31 : $i]:
% 2.32/2.58         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 2.32/2.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 2.32/2.58      inference('demod', [status(thm)], ['41', '42'])).
% 2.32/2.58  thf('44', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 2.32/2.58      inference('demod', [status(thm)], ['40', '43'])).
% 2.32/2.58  thf('45', plain,
% 2.32/2.58      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.32/2.58         = (k6_relat_1 @ sk_A))),
% 2.32/2.58      inference('demod', [status(thm)], ['21', '44'])).
% 2.32/2.58  thf('46', plain,
% 2.32/2.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf(t24_funct_2, axiom,
% 2.32/2.58    (![A:$i,B:$i,C:$i]:
% 2.32/2.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.32/2.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.58       ( ![D:$i]:
% 2.32/2.58         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.32/2.58             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.32/2.58           ( ( r2_relset_1 @
% 2.32/2.58               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.32/2.58               ( k6_partfun1 @ B ) ) =>
% 2.32/2.58             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.32/2.58  thf('47', plain,
% 2.32/2.58      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 2.32/2.58         (~ (v1_funct_1 @ X39)
% 2.32/2.58          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 2.32/2.58          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 2.32/2.58          | ~ (r2_relset_1 @ X40 @ X40 @ 
% 2.32/2.58               (k1_partfun1 @ X40 @ X41 @ X41 @ X40 @ X39 @ X42) @ 
% 2.32/2.58               (k6_partfun1 @ X40))
% 2.32/2.58          | ((k2_relset_1 @ X41 @ X40 @ X42) = (X40))
% 2.32/2.58          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 2.32/2.58          | ~ (v1_funct_2 @ X42 @ X41 @ X40)
% 2.32/2.58          | ~ (v1_funct_1 @ X42))),
% 2.32/2.58      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.32/2.58  thf('48', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 2.32/2.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.32/2.58  thf('49', plain,
% 2.32/2.58      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 2.32/2.58         (~ (v1_funct_1 @ X39)
% 2.32/2.58          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 2.32/2.58          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 2.32/2.58          | ~ (r2_relset_1 @ X40 @ X40 @ 
% 2.32/2.58               (k1_partfun1 @ X40 @ X41 @ X41 @ X40 @ X39 @ X42) @ 
% 2.32/2.58               (k6_relat_1 @ X40))
% 2.32/2.58          | ((k2_relset_1 @ X41 @ X40 @ X42) = (X40))
% 2.32/2.58          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 2.32/2.58          | ~ (v1_funct_2 @ X42 @ X41 @ X40)
% 2.32/2.58          | ~ (v1_funct_1 @ X42))),
% 2.32/2.58      inference('demod', [status(thm)], ['47', '48'])).
% 2.32/2.58  thf('50', plain,
% 2.32/2.58      (![X0 : $i]:
% 2.32/2.58         (~ (v1_funct_1 @ X0)
% 2.32/2.58          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.32/2.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.32/2.58          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.32/2.58          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.32/2.58               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.32/2.58               (k6_relat_1 @ sk_A))
% 2.32/2.58          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.32/2.58          | ~ (v1_funct_1 @ sk_C))),
% 2.32/2.58      inference('sup-', [status(thm)], ['46', '49'])).
% 2.32/2.58  thf('51', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('53', plain,
% 2.32/2.58      (![X0 : $i]:
% 2.32/2.58         (~ (v1_funct_1 @ X0)
% 2.32/2.58          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.32/2.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.32/2.58          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.32/2.58          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.32/2.58               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.32/2.58               (k6_relat_1 @ sk_A)))),
% 2.32/2.58      inference('demod', [status(thm)], ['50', '51', '52'])).
% 2.32/2.58  thf('54', plain,
% 2.32/2.58      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 2.32/2.58           (k6_relat_1 @ sk_A))
% 2.32/2.58        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.32/2.58        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.32/2.58        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.32/2.58        | ~ (v1_funct_1 @ sk_D))),
% 2.32/2.58      inference('sup-', [status(thm)], ['45', '53'])).
% 2.32/2.58  thf('55', plain,
% 2.32/2.58      (![X31 : $i]:
% 2.32/2.58         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 2.32/2.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 2.32/2.58      inference('demod', [status(thm)], ['41', '42'])).
% 2.32/2.58  thf('56', plain,
% 2.32/2.58      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.32/2.58         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 2.32/2.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 2.32/2.58          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 2.32/2.58          | ((X20) != (X23)))),
% 2.32/2.58      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.32/2.58  thf('57', plain,
% 2.32/2.58      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.32/2.58         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 2.32/2.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.32/2.58      inference('simplify', [status(thm)], ['56'])).
% 2.32/2.58  thf('58', plain,
% 2.32/2.58      (![X0 : $i]:
% 2.32/2.58         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 2.32/2.58      inference('sup-', [status(thm)], ['55', '57'])).
% 2.32/2.58  thf('59', plain,
% 2.32/2.58      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.32/2.58      inference('sup-', [status(thm)], ['5', '6'])).
% 2.32/2.58  thf('60', plain,
% 2.32/2.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('61', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('62', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('63', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.32/2.58      inference('demod', [status(thm)], ['54', '58', '59', '60', '61', '62'])).
% 2.32/2.58  thf('64', plain,
% 2.32/2.58      ((((sk_A) != (sk_A))
% 2.32/2.58        | ~ (v2_funct_1 @ sk_D)
% 2.32/2.58        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 2.32/2.58      inference('demod', [status(thm)], ['12', '63'])).
% 2.32/2.58  thf('65', plain,
% 2.32/2.58      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.32/2.58        | ~ (v2_funct_1 @ sk_D))),
% 2.32/2.58      inference('simplify', [status(thm)], ['64'])).
% 2.32/2.58  thf('66', plain,
% 2.32/2.58      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.32/2.58         = (k6_relat_1 @ sk_A))),
% 2.32/2.58      inference('demod', [status(thm)], ['21', '44'])).
% 2.32/2.58  thf('67', plain,
% 2.32/2.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf(t30_funct_2, axiom,
% 2.32/2.58    (![A:$i,B:$i,C:$i,D:$i]:
% 2.32/2.58     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.32/2.58         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 2.32/2.58       ( ![E:$i]:
% 2.32/2.58         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 2.32/2.58             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 2.32/2.58           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.32/2.58               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 2.32/2.58             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 2.32/2.58               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 2.32/2.58  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 2.32/2.58  thf(zf_stmt_2, axiom,
% 2.32/2.58    (![C:$i,B:$i]:
% 2.32/2.58     ( ( zip_tseitin_1 @ C @ B ) =>
% 2.32/2.58       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 2.32/2.58  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.32/2.58  thf(zf_stmt_4, axiom,
% 2.32/2.58    (![E:$i,D:$i]:
% 2.32/2.58     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 2.32/2.58  thf(zf_stmt_5, axiom,
% 2.32/2.58    (![A:$i,B:$i,C:$i,D:$i]:
% 2.32/2.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.32/2.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.58       ( ![E:$i]:
% 2.32/2.58         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.32/2.58             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.32/2.58           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 2.32/2.58               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 2.32/2.58             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 2.32/2.58  thf('68', plain,
% 2.32/2.58      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 2.32/2.58         (~ (v1_funct_1 @ X47)
% 2.32/2.58          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 2.32/2.58          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 2.32/2.58          | (zip_tseitin_0 @ X47 @ X50)
% 2.32/2.58          | ~ (v2_funct_1 @ (k1_partfun1 @ X51 @ X48 @ X48 @ X49 @ X50 @ X47))
% 2.32/2.58          | (zip_tseitin_1 @ X49 @ X48)
% 2.32/2.58          | ((k2_relset_1 @ X51 @ X48 @ X50) != (X48))
% 2.32/2.58          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X48)))
% 2.32/2.58          | ~ (v1_funct_2 @ X50 @ X51 @ X48)
% 2.32/2.58          | ~ (v1_funct_1 @ X50))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.32/2.58  thf('69', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i]:
% 2.32/2.58         (~ (v1_funct_1 @ X0)
% 2.32/2.58          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.32/2.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.32/2.58          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.32/2.58          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.32/2.58          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.32/2.58          | (zip_tseitin_0 @ sk_D @ X0)
% 2.32/2.58          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.32/2.58          | ~ (v1_funct_1 @ sk_D))),
% 2.32/2.58      inference('sup-', [status(thm)], ['67', '68'])).
% 2.32/2.58  thf('70', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('71', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('72', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i]:
% 2.32/2.58         (~ (v1_funct_1 @ X0)
% 2.32/2.58          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.32/2.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.32/2.58          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.32/2.58          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.32/2.58          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.32/2.58          | (zip_tseitin_0 @ sk_D @ X0))),
% 2.32/2.58      inference('demod', [status(thm)], ['69', '70', '71'])).
% 2.32/2.58  thf('73', plain,
% 2.32/2.58      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 2.32/2.58        | (zip_tseitin_0 @ sk_D @ sk_C)
% 2.32/2.58        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.32/2.58        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.32/2.58        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.32/2.58        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.32/2.58        | ~ (v1_funct_1 @ sk_C))),
% 2.32/2.58      inference('sup-', [status(thm)], ['66', '72'])).
% 2.32/2.58  thf(fc4_funct_1, axiom,
% 2.32/2.58    (![A:$i]:
% 2.32/2.58     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.32/2.58       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.32/2.58  thf('74', plain, (![X13 : $i]: (v2_funct_1 @ (k6_relat_1 @ X13))),
% 2.32/2.58      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.32/2.58  thf('75', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('76', plain,
% 2.32/2.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('77', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('79', plain,
% 2.32/2.58      (((zip_tseitin_0 @ sk_D @ sk_C)
% 2.32/2.58        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.32/2.58        | ((sk_B) != (sk_B)))),
% 2.32/2.58      inference('demod', [status(thm)], ['73', '74', '75', '76', '77', '78'])).
% 2.32/2.58  thf('80', plain,
% 2.32/2.58      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 2.32/2.58      inference('simplify', [status(thm)], ['79'])).
% 2.32/2.58  thf('81', plain,
% 2.32/2.58      (![X45 : $i, X46 : $i]:
% 2.32/2.58         (((X45) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X45 @ X46))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.32/2.58  thf('82', plain,
% 2.32/2.58      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.32/2.58      inference('sup-', [status(thm)], ['80', '81'])).
% 2.32/2.58  thf('83', plain, (((sk_A) != (k1_xboole_0))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('84', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 2.32/2.58      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 2.32/2.58  thf('85', plain,
% 2.32/2.58      (![X43 : $i, X44 : $i]:
% 2.32/2.58         ((v2_funct_1 @ X44) | ~ (zip_tseitin_0 @ X44 @ X43))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.32/2.58  thf('86', plain, ((v2_funct_1 @ sk_D)),
% 2.32/2.58      inference('sup-', [status(thm)], ['84', '85'])).
% 2.32/2.58  thf('87', plain,
% 2.32/2.58      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 2.32/2.58      inference('demod', [status(thm)], ['65', '86'])).
% 2.32/2.58  thf('88', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 2.32/2.58      inference('demod', [status(thm)], ['40', '43'])).
% 2.32/2.58  thf(t64_funct_1, axiom,
% 2.32/2.58    (![A:$i]:
% 2.32/2.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.32/2.58       ( ![B:$i]:
% 2.32/2.58         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.32/2.58           ( ( ( v2_funct_1 @ A ) & 
% 2.32/2.58               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 2.32/2.58               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 2.32/2.58             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.32/2.58  thf('89', plain,
% 2.32/2.58      (![X15 : $i, X16 : $i]:
% 2.32/2.58         (~ (v1_relat_1 @ X15)
% 2.32/2.58          | ~ (v1_funct_1 @ X15)
% 2.32/2.58          | ((X15) = (k2_funct_1 @ X16))
% 2.32/2.58          | ((k5_relat_1 @ X15 @ X16) != (k6_relat_1 @ (k2_relat_1 @ X16)))
% 2.32/2.58          | ((k2_relat_1 @ X15) != (k1_relat_1 @ X16))
% 2.32/2.58          | ~ (v2_funct_1 @ X16)
% 2.32/2.58          | ~ (v1_funct_1 @ X16)
% 2.32/2.58          | ~ (v1_relat_1 @ X16))),
% 2.32/2.58      inference('cnf', [status(esa)], [t64_funct_1])).
% 2.32/2.58  thf('90', plain,
% 2.32/2.58      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 2.32/2.58        | ~ (v1_relat_1 @ sk_D)
% 2.32/2.58        | ~ (v1_funct_1 @ sk_D)
% 2.32/2.58        | ~ (v2_funct_1 @ sk_D)
% 2.32/2.58        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 2.32/2.58        | ((sk_C) = (k2_funct_1 @ sk_D))
% 2.32/2.58        | ~ (v1_funct_1 @ sk_C)
% 2.32/2.58        | ~ (v1_relat_1 @ sk_C))),
% 2.32/2.58      inference('sup-', [status(thm)], ['88', '89'])).
% 2.32/2.58  thf('91', plain,
% 2.32/2.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf(cc2_relat_1, axiom,
% 2.32/2.58    (![A:$i]:
% 2.32/2.58     ( ( v1_relat_1 @ A ) =>
% 2.32/2.58       ( ![B:$i]:
% 2.32/2.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.32/2.58  thf('92', plain,
% 2.32/2.58      (![X3 : $i, X4 : $i]:
% 2.32/2.58         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.32/2.58          | (v1_relat_1 @ X3)
% 2.32/2.58          | ~ (v1_relat_1 @ X4))),
% 2.32/2.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.32/2.58  thf('93', plain,
% 2.32/2.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.32/2.58      inference('sup-', [status(thm)], ['91', '92'])).
% 2.32/2.58  thf(fc6_relat_1, axiom,
% 2.32/2.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.32/2.58  thf('94', plain,
% 2.32/2.58      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 2.32/2.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.32/2.58  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 2.32/2.58      inference('demod', [status(thm)], ['93', '94'])).
% 2.32/2.58  thf('96', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('97', plain,
% 2.32/2.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('98', plain,
% 2.32/2.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.32/2.58         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 2.32/2.58          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 2.32/2.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.32/2.58  thf('99', plain,
% 2.32/2.58      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.32/2.58      inference('sup-', [status(thm)], ['97', '98'])).
% 2.32/2.58  thf('100', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('101', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.32/2.58      inference('sup+', [status(thm)], ['99', '100'])).
% 2.32/2.58  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('103', plain,
% 2.32/2.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('104', plain,
% 2.32/2.58      (![X3 : $i, X4 : $i]:
% 2.32/2.58         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.32/2.58          | (v1_relat_1 @ X3)
% 2.32/2.58          | ~ (v1_relat_1 @ X4))),
% 2.32/2.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.32/2.58  thf('105', plain,
% 2.32/2.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.32/2.58      inference('sup-', [status(thm)], ['103', '104'])).
% 2.32/2.58  thf('106', plain,
% 2.32/2.58      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 2.32/2.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.32/2.58  thf('107', plain, ((v1_relat_1 @ sk_C)),
% 2.32/2.58      inference('demod', [status(thm)], ['105', '106'])).
% 2.32/2.58  thf('108', plain,
% 2.32/2.58      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 2.32/2.58        | ~ (v2_funct_1 @ sk_D)
% 2.32/2.58        | ((sk_B) != (k1_relat_1 @ sk_D))
% 2.32/2.58        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 2.32/2.58      inference('demod', [status(thm)], ['90', '95', '96', '101', '102', '107'])).
% 2.32/2.58  thf('109', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.32/2.58      inference('demod', [status(thm)], ['54', '58', '59', '60', '61', '62'])).
% 2.32/2.58  thf('110', plain,
% 2.32/2.58      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 2.32/2.58        | ~ (v2_funct_1 @ sk_D)
% 2.32/2.58        | ((sk_B) != (k1_relat_1 @ sk_D))
% 2.32/2.58        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 2.32/2.58      inference('demod', [status(thm)], ['108', '109'])).
% 2.32/2.58  thf('111', plain,
% 2.32/2.58      ((((sk_C) = (k2_funct_1 @ sk_D))
% 2.32/2.58        | ((sk_B) != (k1_relat_1 @ sk_D))
% 2.32/2.58        | ~ (v2_funct_1 @ sk_D))),
% 2.32/2.58      inference('simplify', [status(thm)], ['110'])).
% 2.32/2.58  thf('112', plain, ((v2_funct_1 @ sk_D)),
% 2.32/2.58      inference('sup-', [status(thm)], ['84', '85'])).
% 2.32/2.58  thf('113', plain,
% 2.32/2.58      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 2.32/2.58      inference('demod', [status(thm)], ['111', '112'])).
% 2.32/2.58  thf('114', plain,
% 2.32/2.58      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 2.32/2.58      inference('demod', [status(thm)], ['65', '86'])).
% 2.32/2.58  thf(dt_k2_funct_1, axiom,
% 2.32/2.58    (![A:$i]:
% 2.32/2.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.32/2.58       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.32/2.58         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.32/2.58  thf('115', plain,
% 2.32/2.58      (![X11 : $i]:
% 2.32/2.58         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 2.32/2.58          | ~ (v1_funct_1 @ X11)
% 2.32/2.58          | ~ (v1_relat_1 @ X11))),
% 2.32/2.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.32/2.58  thf(d10_xboole_0, axiom,
% 2.32/2.58    (![A:$i,B:$i]:
% 2.32/2.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.32/2.58  thf('116', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.32/2.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.32/2.58  thf('117', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.32/2.58      inference('simplify', [status(thm)], ['116'])).
% 2.32/2.58  thf(t55_funct_1, axiom,
% 2.32/2.58    (![A:$i]:
% 2.32/2.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.32/2.58       ( ( v2_funct_1 @ A ) =>
% 2.32/2.58         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.32/2.58           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.32/2.58  thf('118', plain,
% 2.32/2.58      (![X14 : $i]:
% 2.32/2.58         (~ (v2_funct_1 @ X14)
% 2.32/2.58          | ((k2_relat_1 @ X14) = (k1_relat_1 @ (k2_funct_1 @ X14)))
% 2.32/2.58          | ~ (v1_funct_1 @ X14)
% 2.32/2.58          | ~ (v1_relat_1 @ X14))),
% 2.32/2.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.32/2.58  thf(t46_relat_1, axiom,
% 2.32/2.58    (![A:$i]:
% 2.32/2.58     ( ( v1_relat_1 @ A ) =>
% 2.32/2.58       ( ![B:$i]:
% 2.32/2.58         ( ( v1_relat_1 @ B ) =>
% 2.32/2.58           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 2.32/2.58             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 2.32/2.58  thf('119', plain,
% 2.32/2.58      (![X7 : $i, X8 : $i]:
% 2.32/2.58         (~ (v1_relat_1 @ X7)
% 2.32/2.58          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7)) = (k1_relat_1 @ X8))
% 2.32/2.58          | ~ (r1_tarski @ (k2_relat_1 @ X8) @ (k1_relat_1 @ X7))
% 2.32/2.58          | ~ (v1_relat_1 @ X8))),
% 2.32/2.58      inference('cnf', [status(esa)], [t46_relat_1])).
% 2.32/2.58  thf('120', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i]:
% 2.32/2.58         (~ (r1_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))
% 2.32/2.58          | ~ (v1_relat_1 @ X0)
% 2.32/2.58          | ~ (v1_funct_1 @ X0)
% 2.32/2.58          | ~ (v2_funct_1 @ X0)
% 2.32/2.58          | ~ (v1_relat_1 @ X1)
% 2.32/2.58          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X0)))
% 2.32/2.58              = (k1_relat_1 @ X1))
% 2.32/2.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.32/2.58      inference('sup-', [status(thm)], ['118', '119'])).
% 2.32/2.58  thf('121', plain,
% 2.32/2.58      (![X0 : $i]:
% 2.32/2.58         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.32/2.58          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 2.32/2.58              = (k1_relat_1 @ X0))
% 2.32/2.58          | ~ (v1_relat_1 @ X0)
% 2.32/2.58          | ~ (v2_funct_1 @ X0)
% 2.32/2.58          | ~ (v1_funct_1 @ X0)
% 2.32/2.58          | ~ (v1_relat_1 @ X0))),
% 2.32/2.58      inference('sup-', [status(thm)], ['117', '120'])).
% 2.32/2.58  thf('122', plain,
% 2.32/2.58      (![X0 : $i]:
% 2.32/2.58         (~ (v1_funct_1 @ X0)
% 2.32/2.58          | ~ (v2_funct_1 @ X0)
% 2.32/2.58          | ~ (v1_relat_1 @ X0)
% 2.32/2.58          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 2.32/2.58              = (k1_relat_1 @ X0))
% 2.32/2.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.32/2.58      inference('simplify', [status(thm)], ['121'])).
% 2.32/2.58  thf('123', plain,
% 2.32/2.58      (![X0 : $i]:
% 2.32/2.58         (~ (v1_relat_1 @ X0)
% 2.32/2.58          | ~ (v1_funct_1 @ X0)
% 2.32/2.58          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 2.32/2.58              = (k1_relat_1 @ X0))
% 2.32/2.58          | ~ (v1_relat_1 @ X0)
% 2.32/2.58          | ~ (v2_funct_1 @ X0)
% 2.32/2.58          | ~ (v1_funct_1 @ X0))),
% 2.32/2.58      inference('sup-', [status(thm)], ['115', '122'])).
% 2.32/2.58  thf('124', plain,
% 2.32/2.58      (![X0 : $i]:
% 2.32/2.58         (~ (v2_funct_1 @ X0)
% 2.32/2.58          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 2.32/2.58              = (k1_relat_1 @ X0))
% 2.32/2.58          | ~ (v1_funct_1 @ X0)
% 2.32/2.58          | ~ (v1_relat_1 @ X0))),
% 2.32/2.58      inference('simplify', [status(thm)], ['123'])).
% 2.32/2.58  thf('125', plain,
% 2.32/2.58      ((((k1_relat_1 @ (k6_relat_1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 2.32/2.58        | ~ (v1_relat_1 @ sk_D)
% 2.32/2.58        | ~ (v1_funct_1 @ sk_D)
% 2.32/2.58        | ~ (v2_funct_1 @ sk_D))),
% 2.32/2.58      inference('sup+', [status(thm)], ['114', '124'])).
% 2.32/2.58  thf(t71_relat_1, axiom,
% 2.32/2.58    (![A:$i]:
% 2.32/2.58     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.32/2.58       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.32/2.58  thf('126', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 2.32/2.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.32/2.58  thf('127', plain, ((v1_relat_1 @ sk_D)),
% 2.32/2.58      inference('demod', [status(thm)], ['93', '94'])).
% 2.32/2.58  thf('128', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('129', plain, ((v2_funct_1 @ sk_D)),
% 2.32/2.58      inference('sup-', [status(thm)], ['84', '85'])).
% 2.32/2.58  thf('130', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 2.32/2.58      inference('demod', [status(thm)], ['125', '126', '127', '128', '129'])).
% 2.32/2.58  thf('131', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 2.32/2.58      inference('demod', [status(thm)], ['113', '130'])).
% 2.32/2.58  thf('132', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 2.32/2.58      inference('simplify', [status(thm)], ['131'])).
% 2.32/2.58  thf('133', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 2.32/2.58      inference('demod', [status(thm)], ['87', '132'])).
% 2.32/2.58  thf('134', plain,
% 2.32/2.58      (![X15 : $i, X16 : $i]:
% 2.32/2.58         (~ (v1_relat_1 @ X15)
% 2.32/2.58          | ~ (v1_funct_1 @ X15)
% 2.32/2.58          | ((X15) = (k2_funct_1 @ X16))
% 2.32/2.58          | ((k5_relat_1 @ X15 @ X16) != (k6_relat_1 @ (k2_relat_1 @ X16)))
% 2.32/2.58          | ((k2_relat_1 @ X15) != (k1_relat_1 @ X16))
% 2.32/2.58          | ~ (v2_funct_1 @ X16)
% 2.32/2.58          | ~ (v1_funct_1 @ X16)
% 2.32/2.58          | ~ (v1_relat_1 @ X16))),
% 2.32/2.58      inference('cnf', [status(esa)], [t64_funct_1])).
% 2.32/2.58  thf('135', plain,
% 2.32/2.58      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 2.32/2.58        | ~ (v1_relat_1 @ sk_C)
% 2.32/2.58        | ~ (v1_funct_1 @ sk_C)
% 2.32/2.58        | ~ (v2_funct_1 @ sk_C)
% 2.32/2.58        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_C))
% 2.32/2.58        | ((sk_D) = (k2_funct_1 @ sk_C))
% 2.32/2.58        | ~ (v1_funct_1 @ sk_D)
% 2.32/2.58        | ~ (v1_relat_1 @ sk_D))),
% 2.32/2.58      inference('sup-', [status(thm)], ['133', '134'])).
% 2.32/2.58  thf('136', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.32/2.58      inference('sup+', [status(thm)], ['99', '100'])).
% 2.32/2.58  thf('137', plain, ((v1_relat_1 @ sk_C)),
% 2.32/2.58      inference('demod', [status(thm)], ['105', '106'])).
% 2.32/2.58  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('139', plain, ((v2_funct_1 @ sk_C)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('140', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.32/2.58      inference('demod', [status(thm)], ['54', '58', '59', '60', '61', '62'])).
% 2.32/2.58  thf('141', plain,
% 2.32/2.58      (![X11 : $i]:
% 2.32/2.58         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 2.32/2.58          | ~ (v1_funct_1 @ X11)
% 2.32/2.58          | ~ (v1_relat_1 @ X11))),
% 2.32/2.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.32/2.58  thf('142', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.32/2.58      inference('sup+', [status(thm)], ['99', '100'])).
% 2.32/2.58  thf('143', plain,
% 2.32/2.58      (![X14 : $i]:
% 2.32/2.58         (~ (v2_funct_1 @ X14)
% 2.32/2.58          | ((k2_relat_1 @ X14) = (k1_relat_1 @ (k2_funct_1 @ X14)))
% 2.32/2.58          | ~ (v1_funct_1 @ X14)
% 2.32/2.58          | ~ (v1_relat_1 @ X14))),
% 2.32/2.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.32/2.58  thf('144', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.32/2.58      inference('sup+', [status(thm)], ['99', '100'])).
% 2.32/2.58  thf('145', plain,
% 2.32/2.58      (![X7 : $i, X8 : $i]:
% 2.32/2.58         (~ (v1_relat_1 @ X7)
% 2.32/2.58          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7)) = (k1_relat_1 @ X8))
% 2.32/2.58          | ~ (r1_tarski @ (k2_relat_1 @ X8) @ (k1_relat_1 @ X7))
% 2.32/2.58          | ~ (v1_relat_1 @ X8))),
% 2.32/2.58      inference('cnf', [status(esa)], [t46_relat_1])).
% 2.32/2.58  thf('146', plain,
% 2.32/2.58      (![X0 : $i]:
% 2.32/2.58         (~ (r1_tarski @ sk_B @ (k1_relat_1 @ X0))
% 2.32/2.58          | ~ (v1_relat_1 @ sk_C)
% 2.32/2.58          | ((k1_relat_1 @ (k5_relat_1 @ sk_C @ X0)) = (k1_relat_1 @ sk_C))
% 2.32/2.58          | ~ (v1_relat_1 @ X0))),
% 2.32/2.58      inference('sup-', [status(thm)], ['144', '145'])).
% 2.32/2.58  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 2.32/2.58      inference('demod', [status(thm)], ['105', '106'])).
% 2.32/2.58  thf('148', plain,
% 2.32/2.58      (![X0 : $i]:
% 2.32/2.58         (~ (r1_tarski @ sk_B @ (k1_relat_1 @ X0))
% 2.32/2.58          | ((k1_relat_1 @ (k5_relat_1 @ sk_C @ X0)) = (k1_relat_1 @ sk_C))
% 2.32/2.58          | ~ (v1_relat_1 @ X0))),
% 2.32/2.58      inference('demod', [status(thm)], ['146', '147'])).
% 2.32/2.58  thf('149', plain,
% 2.32/2.58      (![X0 : $i]:
% 2.32/2.58         (~ (r1_tarski @ sk_B @ (k2_relat_1 @ X0))
% 2.32/2.58          | ~ (v1_relat_1 @ X0)
% 2.32/2.58          | ~ (v1_funct_1 @ X0)
% 2.32/2.58          | ~ (v2_funct_1 @ X0)
% 2.32/2.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.32/2.58          | ((k1_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ X0)))
% 2.32/2.58              = (k1_relat_1 @ sk_C)))),
% 2.32/2.58      inference('sup-', [status(thm)], ['143', '148'])).
% 2.32/2.58  thf('150', plain,
% 2.32/2.58      ((~ (r1_tarski @ sk_B @ sk_B)
% 2.32/2.58        | ((k1_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 2.32/2.58            = (k1_relat_1 @ sk_C))
% 2.32/2.58        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.32/2.58        | ~ (v2_funct_1 @ sk_C)
% 2.32/2.58        | ~ (v1_funct_1 @ sk_C)
% 2.32/2.58        | ~ (v1_relat_1 @ sk_C))),
% 2.32/2.58      inference('sup-', [status(thm)], ['142', '149'])).
% 2.32/2.58  thf('151', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.32/2.58      inference('simplify', [status(thm)], ['116'])).
% 2.32/2.58  thf('152', plain, ((v2_funct_1 @ sk_C)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('153', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('154', plain, ((v1_relat_1 @ sk_C)),
% 2.32/2.58      inference('demod', [status(thm)], ['105', '106'])).
% 2.32/2.58  thf('155', plain,
% 2.32/2.58      ((((k1_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 2.32/2.58          = (k1_relat_1 @ sk_C))
% 2.32/2.58        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.32/2.58      inference('demod', [status(thm)], ['150', '151', '152', '153', '154'])).
% 2.32/2.58  thf('156', plain,
% 2.32/2.58      ((~ (v1_relat_1 @ sk_C)
% 2.32/2.58        | ~ (v1_funct_1 @ sk_C)
% 2.32/2.58        | ((k1_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 2.32/2.58            = (k1_relat_1 @ sk_C)))),
% 2.32/2.58      inference('sup-', [status(thm)], ['141', '155'])).
% 2.32/2.58  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 2.32/2.58      inference('demod', [status(thm)], ['105', '106'])).
% 2.32/2.58  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('159', plain,
% 2.32/2.58      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 2.32/2.58         = (k1_relat_1 @ sk_C))),
% 2.32/2.58      inference('demod', [status(thm)], ['156', '157', '158'])).
% 2.32/2.58  thf('160', plain,
% 2.32/2.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('161', plain,
% 2.32/2.58      (![X52 : $i, X53 : $i, X54 : $i]:
% 2.32/2.58         (((X52) = (k1_xboole_0))
% 2.32/2.58          | ~ (v1_funct_1 @ X53)
% 2.32/2.58          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 2.32/2.58          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 2.32/2.58          | ((k5_relat_1 @ X53 @ (k2_funct_1 @ X53)) = (k6_relat_1 @ X54))
% 2.32/2.58          | ~ (v2_funct_1 @ X53)
% 2.32/2.58          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 2.32/2.58      inference('demod', [status(thm)], ['1', '2'])).
% 2.32/2.58  thf('162', plain,
% 2.32/2.58      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.32/2.58        | ~ (v2_funct_1 @ sk_C)
% 2.32/2.58        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 2.32/2.58        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.32/2.58        | ~ (v1_funct_1 @ sk_C)
% 2.32/2.58        | ((sk_B) = (k1_xboole_0)))),
% 2.32/2.58      inference('sup-', [status(thm)], ['160', '161'])).
% 2.32/2.58  thf('163', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('164', plain, ((v2_funct_1 @ sk_C)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('165', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('166', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('167', plain,
% 2.32/2.58      ((((sk_B) != (sk_B))
% 2.32/2.58        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 2.32/2.58        | ((sk_B) = (k1_xboole_0)))),
% 2.32/2.58      inference('demod', [status(thm)], ['162', '163', '164', '165', '166'])).
% 2.32/2.58  thf('168', plain,
% 2.32/2.58      ((((sk_B) = (k1_xboole_0))
% 2.32/2.58        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 2.32/2.58      inference('simplify', [status(thm)], ['167'])).
% 2.32/2.58  thf('169', plain, (((sk_B) != (k1_xboole_0))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('170', plain,
% 2.32/2.58      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 2.32/2.58      inference('simplify_reflect-', [status(thm)], ['168', '169'])).
% 2.32/2.58  thf('171', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 2.32/2.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.32/2.58  thf('172', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 2.32/2.58      inference('demod', [status(thm)], ['159', '170', '171'])).
% 2.32/2.58  thf('173', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('174', plain, ((v1_relat_1 @ sk_D)),
% 2.32/2.58      inference('demod', [status(thm)], ['93', '94'])).
% 2.32/2.58  thf('175', plain,
% 2.32/2.58      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 2.32/2.58        | ((sk_A) != (sk_A))
% 2.32/2.58        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 2.32/2.58      inference('demod', [status(thm)],
% 2.32/2.58                ['135', '136', '137', '138', '139', '140', '172', '173', '174'])).
% 2.32/2.58  thf('176', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 2.32/2.58      inference('simplify', [status(thm)], ['175'])).
% 2.32/2.58  thf('177', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('178', plain, ($false),
% 2.32/2.58      inference('simplify_reflect-', [status(thm)], ['176', '177'])).
% 2.32/2.58  
% 2.32/2.58  % SZS output end Refutation
% 2.32/2.58  
% 2.41/2.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
