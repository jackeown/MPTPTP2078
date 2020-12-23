%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pVBY6R4nu5

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:08 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 611 expanded)
%              Number of leaves         :   44 ( 199 expanded)
%              Depth                    :   23
%              Number of atoms          : 1702 (15542 expanded)
%              Number of equality atoms :  113 (1016 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

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

thf('1',plain,(
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

thf('2',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('21',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','24'])).

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

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X8 @ X9 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('27',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X8 @ X9 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_partfun1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','41','44','45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('50',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('51',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','48','51','52','57','58','61'])).

thf('63',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('65',plain,(
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

thf('66',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( zip_tseitin_0 @ X43 @ X46 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X47 @ X44 @ X44 @ X45 @ X46 @ X43 ) )
      | ( zip_tseitin_1 @ X45 @ X44 )
      | ( ( k2_relset_1 @ X47 @ X44 @ X46 )
       != X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('67',plain,(
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
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('72',plain,(
    ! [X4: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('73',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('74',plain,(
    ! [X4: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X4 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

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
    inference(demod,[status(thm)],['71','74','75','76','77','78'])).

thf('80',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X41 @ X42 ) ) ),
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
    ! [X39: $i,X40: $i] :
      ( ( v2_funct_1 @ X40 )
      | ~ ( zip_tseitin_0 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('86',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['63','86'])).

thf('88',plain,(
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

thf('89',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('90',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('92',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','41','44','45','46','47'])).

thf('98',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('101',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('102',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X7 @ ( k2_funct_1 @ X7 ) ) )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('103',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('104',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('105',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('106',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('108',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('110',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['103','106','107','108','109'])).

thf('111',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['87','110'])).

thf('112',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['111'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('113',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('114',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('116',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('118',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['114','115','116','117'])).

thf('119',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['118','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pVBY6R4nu5
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:21:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.74/0.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/0.95  % Solved by: fo/fo7.sh
% 0.74/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.95  % done 880 iterations in 0.480s
% 0.74/0.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/0.95  % SZS output start Refutation
% 0.74/0.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.74/0.95  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.74/0.95  thf(sk_C_type, type, sk_C: $i).
% 0.74/0.95  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.74/0.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.74/0.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.74/0.95  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.74/0.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.74/0.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.74/0.95  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.74/0.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.95  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.74/0.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.95  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.74/0.95  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.74/0.95  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.74/0.95  thf(sk_D_type, type, sk_D: $i).
% 0.74/0.95  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.74/0.95  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.74/0.95  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.74/0.95  thf(t36_funct_2, conjecture,
% 0.74/0.95    (![A:$i,B:$i,C:$i]:
% 0.74/0.95     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.74/0.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.74/0.95       ( ![D:$i]:
% 0.74/0.95         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.74/0.95             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.74/0.95           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.74/0.95               ( r2_relset_1 @
% 0.74/0.95                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.74/0.95                 ( k6_partfun1 @ A ) ) & 
% 0.74/0.95               ( v2_funct_1 @ C ) ) =>
% 0.74/0.95             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.74/0.95               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.74/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.95    (~( ![A:$i,B:$i,C:$i]:
% 0.74/0.95        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.74/0.95            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.74/0.95          ( ![D:$i]:
% 0.74/0.95            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.74/0.95                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.74/0.95              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.74/0.95                  ( r2_relset_1 @
% 0.74/0.95                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.74/0.95                    ( k6_partfun1 @ A ) ) & 
% 0.74/0.95                  ( v2_funct_1 @ C ) ) =>
% 0.74/0.95                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.74/0.95                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.74/0.95    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.74/0.95  thf('0', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('1', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf(redefinition_k1_partfun1, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.74/0.95     ( ( ( v1_funct_1 @ E ) & 
% 0.74/0.95         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.74/0.95         ( v1_funct_1 @ F ) & 
% 0.74/0.95         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.74/0.95       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.74/0.95  thf('2', plain,
% 0.74/0.95      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.74/0.95          | ~ (v1_funct_1 @ X28)
% 0.74/0.95          | ~ (v1_funct_1 @ X31)
% 0.74/0.95          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.74/0.95          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 0.74/0.95              = (k5_relat_1 @ X28 @ X31)))),
% 0.74/0.95      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.74/0.95  thf('3', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.74/0.95            = (k5_relat_1 @ sk_C @ X0))
% 0.74/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.74/0.95          | ~ (v1_funct_1 @ X0)
% 0.74/0.95          | ~ (v1_funct_1 @ sk_C))),
% 0.74/0.95      inference('sup-', [status(thm)], ['1', '2'])).
% 0.74/0.95  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('5', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.74/0.95            = (k5_relat_1 @ sk_C @ X0))
% 0.74/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.74/0.95          | ~ (v1_funct_1 @ X0))),
% 0.74/0.95      inference('demod', [status(thm)], ['3', '4'])).
% 0.74/0.95  thf('6', plain,
% 0.74/0.95      ((~ (v1_funct_1 @ sk_D)
% 0.74/0.95        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.74/0.95            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['0', '5'])).
% 0.74/0.95  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('8', plain,
% 0.74/0.95      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.95        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.74/0.95        (k6_partfun1 @ sk_A))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('9', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('10', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf(dt_k1_partfun1, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.74/0.95     ( ( ( v1_funct_1 @ E ) & 
% 0.74/0.95         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.74/0.95         ( v1_funct_1 @ F ) & 
% 0.74/0.95         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.74/0.95       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.74/0.95         ( m1_subset_1 @
% 0.74/0.95           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.74/0.95           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.74/0.95  thf('11', plain,
% 0.74/0.95      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.74/0.95          | ~ (v1_funct_1 @ X22)
% 0.74/0.95          | ~ (v1_funct_1 @ X25)
% 0.74/0.95          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.74/0.95          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 0.74/0.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 0.74/0.95      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.74/0.95  thf('12', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.74/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.74/0.95          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.74/0.95          | ~ (v1_funct_1 @ X1)
% 0.74/0.95          | ~ (v1_funct_1 @ sk_C))),
% 0.74/0.95      inference('sup-', [status(thm)], ['10', '11'])).
% 0.74/0.95  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('14', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.74/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.74/0.95          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.74/0.95          | ~ (v1_funct_1 @ X1))),
% 0.74/0.95      inference('demod', [status(thm)], ['12', '13'])).
% 0.74/0.95  thf('15', plain,
% 0.74/0.95      ((~ (v1_funct_1 @ sk_D)
% 0.74/0.95        | (m1_subset_1 @ 
% 0.74/0.95           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.74/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.74/0.95      inference('sup-', [status(thm)], ['9', '14'])).
% 0.74/0.95  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('17', plain,
% 0.74/0.95      ((m1_subset_1 @ 
% 0.74/0.95        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.74/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.74/0.95      inference('demod', [status(thm)], ['15', '16'])).
% 0.74/0.95  thf(redefinition_r2_relset_1, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.95     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.74/0.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.74/0.95       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.74/0.95  thf('18', plain,
% 0.74/0.95      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.74/0.95          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.74/0.95          | ((X17) = (X20))
% 0.74/0.95          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 0.74/0.95      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.74/0.95  thf('19', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.95             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.74/0.95          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.74/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.74/0.95      inference('sup-', [status(thm)], ['17', '18'])).
% 0.74/0.95  thf('20', plain,
% 0.74/0.95      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.74/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.74/0.95        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.74/0.95            = (k6_partfun1 @ sk_A)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['8', '19'])).
% 0.74/0.95  thf(t29_relset_1, axiom,
% 0.74/0.95    (![A:$i]:
% 0.74/0.95     ( m1_subset_1 @
% 0.74/0.95       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.74/0.95  thf('21', plain,
% 0.74/0.95      (![X21 : $i]:
% 0.74/0.95         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 0.74/0.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 0.74/0.95      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.74/0.95  thf(redefinition_k6_partfun1, axiom,
% 0.74/0.95    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.74/0.95  thf('22', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.74/0.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.74/0.95  thf('23', plain,
% 0.74/0.95      (![X21 : $i]:
% 0.74/0.95         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 0.74/0.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 0.74/0.95      inference('demod', [status(thm)], ['21', '22'])).
% 0.74/0.95  thf('24', plain,
% 0.74/0.95      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.74/0.95         = (k6_partfun1 @ sk_A))),
% 0.74/0.95      inference('demod', [status(thm)], ['20', '23'])).
% 0.74/0.95  thf('25', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.74/0.95      inference('demod', [status(thm)], ['6', '7', '24'])).
% 0.74/0.95  thf(t64_funct_1, axiom,
% 0.74/0.95    (![A:$i]:
% 0.74/0.95     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.74/0.95       ( ![B:$i]:
% 0.74/0.95         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.74/0.95           ( ( ( v2_funct_1 @ A ) & 
% 0.74/0.95               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.74/0.95               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.74/0.95             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.74/0.95  thf('26', plain,
% 0.74/0.95      (![X8 : $i, X9 : $i]:
% 0.74/0.95         (~ (v1_relat_1 @ X8)
% 0.74/0.95          | ~ (v1_funct_1 @ X8)
% 0.74/0.95          | ((X8) = (k2_funct_1 @ X9))
% 0.74/0.95          | ((k5_relat_1 @ X8 @ X9) != (k6_relat_1 @ (k2_relat_1 @ X9)))
% 0.74/0.95          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 0.74/0.95          | ~ (v2_funct_1 @ X9)
% 0.74/0.95          | ~ (v1_funct_1 @ X9)
% 0.74/0.95          | ~ (v1_relat_1 @ X9))),
% 0.74/0.95      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.74/0.95  thf('27', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.74/0.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.74/0.95  thf('28', plain,
% 0.74/0.95      (![X8 : $i, X9 : $i]:
% 0.74/0.95         (~ (v1_relat_1 @ X8)
% 0.74/0.95          | ~ (v1_funct_1 @ X8)
% 0.74/0.95          | ((X8) = (k2_funct_1 @ X9))
% 0.74/0.95          | ((k5_relat_1 @ X8 @ X9) != (k6_partfun1 @ (k2_relat_1 @ X9)))
% 0.74/0.95          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 0.74/0.95          | ~ (v2_funct_1 @ X9)
% 0.74/0.95          | ~ (v1_funct_1 @ X9)
% 0.74/0.95          | ~ (v1_relat_1 @ X9))),
% 0.74/0.95      inference('demod', [status(thm)], ['26', '27'])).
% 0.74/0.95  thf('29', plain,
% 0.74/0.95      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.74/0.95        | ~ (v1_relat_1 @ sk_D)
% 0.74/0.95        | ~ (v1_funct_1 @ sk_D)
% 0.74/0.95        | ~ (v2_funct_1 @ sk_D)
% 0.74/0.95        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.74/0.95        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.74/0.95        | ~ (v1_funct_1 @ sk_C)
% 0.74/0.95        | ~ (v1_relat_1 @ sk_C))),
% 0.74/0.95      inference('sup-', [status(thm)], ['25', '28'])).
% 0.74/0.95  thf('30', plain,
% 0.74/0.95      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.74/0.95         = (k6_partfun1 @ sk_A))),
% 0.74/0.95      inference('demod', [status(thm)], ['20', '23'])).
% 0.74/0.95  thf('31', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf(t24_funct_2, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i]:
% 0.74/0.95     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.74/0.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.74/0.95       ( ![D:$i]:
% 0.74/0.95         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.74/0.95             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.74/0.95           ( ( r2_relset_1 @
% 0.74/0.95               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.74/0.95               ( k6_partfun1 @ B ) ) =>
% 0.74/0.95             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.74/0.95  thf('32', plain,
% 0.74/0.95      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.74/0.95         (~ (v1_funct_1 @ X35)
% 0.74/0.95          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 0.74/0.95          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.74/0.95          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 0.74/0.95               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 0.74/0.95               (k6_partfun1 @ X36))
% 0.74/0.95          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 0.74/0.95          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.74/0.95          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 0.74/0.95          | ~ (v1_funct_1 @ X38))),
% 0.74/0.95      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.74/0.95  thf('33', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (~ (v1_funct_1 @ X0)
% 0.74/0.95          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.74/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.74/0.95          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.74/0.95          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.95               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.74/0.95               (k6_partfun1 @ sk_A))
% 0.74/0.95          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.74/0.95          | ~ (v1_funct_1 @ sk_C))),
% 0.74/0.95      inference('sup-', [status(thm)], ['31', '32'])).
% 0.74/0.95  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('36', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (~ (v1_funct_1 @ X0)
% 0.74/0.95          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.74/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.74/0.95          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.74/0.95          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.95               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.74/0.95               (k6_partfun1 @ sk_A)))),
% 0.74/0.95      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.74/0.95  thf('37', plain,
% 0.74/0.95      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.74/0.95           (k6_partfun1 @ sk_A))
% 0.74/0.95        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.74/0.95        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.74/0.95        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.74/0.95        | ~ (v1_funct_1 @ sk_D))),
% 0.74/0.95      inference('sup-', [status(thm)], ['30', '36'])).
% 0.74/0.95  thf('38', plain,
% 0.74/0.95      (![X21 : $i]:
% 0.74/0.95         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 0.74/0.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 0.74/0.95      inference('demod', [status(thm)], ['21', '22'])).
% 0.74/0.95  thf('39', plain,
% 0.74/0.95      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.74/0.95          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.74/0.95          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 0.74/0.95          | ((X17) != (X20)))),
% 0.74/0.95      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.74/0.95  thf('40', plain,
% 0.74/0.95      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.74/0.95         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 0.74/0.95          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.74/0.95      inference('simplify', [status(thm)], ['39'])).
% 0.74/0.95  thf('41', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.74/0.95      inference('sup-', [status(thm)], ['38', '40'])).
% 0.74/0.95  thf('42', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf(redefinition_k2_relset_1, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i]:
% 0.74/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.95       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.74/0.95  thf('43', plain,
% 0.74/0.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.74/0.95         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.74/0.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.74/0.95      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.74/0.95  thf('44', plain,
% 0.74/0.95      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.74/0.95      inference('sup-', [status(thm)], ['42', '43'])).
% 0.74/0.95  thf('45', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.74/0.95      inference('demod', [status(thm)], ['37', '41', '44', '45', '46', '47'])).
% 0.74/0.95  thf('49', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf(cc1_relset_1, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i]:
% 0.74/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.95       ( v1_relat_1 @ C ) ))).
% 0.74/0.95  thf('50', plain,
% 0.74/0.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.74/0.95         ((v1_relat_1 @ X11)
% 0.74/0.95          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.74/0.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.74/0.95  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 0.74/0.95      inference('sup-', [status(thm)], ['49', '50'])).
% 0.74/0.95  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('53', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('54', plain,
% 0.74/0.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.74/0.95         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.74/0.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.74/0.95      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.74/0.95  thf('55', plain,
% 0.74/0.95      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.74/0.95      inference('sup-', [status(thm)], ['53', '54'])).
% 0.74/0.95  thf('56', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('57', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.74/0.95      inference('sup+', [status(thm)], ['55', '56'])).
% 0.74/0.95  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('59', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('60', plain,
% 0.74/0.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.74/0.95         ((v1_relat_1 @ X11)
% 0.74/0.95          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.74/0.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.74/0.95  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.74/0.95      inference('sup-', [status(thm)], ['59', '60'])).
% 0.74/0.95  thf('62', plain,
% 0.74/0.95      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.74/0.95        | ~ (v2_funct_1 @ sk_D)
% 0.74/0.95        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.74/0.95        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.74/0.95      inference('demod', [status(thm)],
% 0.74/0.95                ['29', '48', '51', '52', '57', '58', '61'])).
% 0.74/0.95  thf('63', plain,
% 0.74/0.95      ((((sk_C) = (k2_funct_1 @ sk_D))
% 0.74/0.95        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.74/0.95        | ~ (v2_funct_1 @ sk_D))),
% 0.74/0.95      inference('simplify', [status(thm)], ['62'])).
% 0.74/0.95  thf('64', plain,
% 0.74/0.95      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.74/0.95         = (k6_partfun1 @ sk_A))),
% 0.74/0.95      inference('demod', [status(thm)], ['20', '23'])).
% 0.74/0.95  thf('65', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf(t30_funct_2, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.95     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.74/0.95         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.74/0.95       ( ![E:$i]:
% 0.74/0.95         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 0.74/0.95             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 0.74/0.95           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.74/0.95               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 0.74/0.95             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 0.74/0.95               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.74/0.95  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.74/0.95  thf(zf_stmt_2, axiom,
% 0.74/0.95    (![C:$i,B:$i]:
% 0.74/0.95     ( ( zip_tseitin_1 @ C @ B ) =>
% 0.74/0.95       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.74/0.95  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.74/0.95  thf(zf_stmt_4, axiom,
% 0.74/0.95    (![E:$i,D:$i]:
% 0.74/0.95     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 0.74/0.95  thf(zf_stmt_5, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.95     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.74/0.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.74/0.95       ( ![E:$i]:
% 0.74/0.95         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.74/0.95             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.74/0.95           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 0.74/0.95               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 0.74/0.95             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 0.74/0.95  thf('66', plain,
% 0.74/0.95      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.74/0.95         (~ (v1_funct_1 @ X43)
% 0.74/0.95          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.74/0.95          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.74/0.95          | (zip_tseitin_0 @ X43 @ X46)
% 0.74/0.95          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X44 @ X44 @ X45 @ X46 @ X43))
% 0.74/0.95          | (zip_tseitin_1 @ X45 @ X44)
% 0.74/0.95          | ((k2_relset_1 @ X47 @ X44 @ X46) != (X44))
% 0.74/0.95          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X44)))
% 0.74/0.95          | ~ (v1_funct_2 @ X46 @ X47 @ X44)
% 0.74/0.95          | ~ (v1_funct_1 @ X46))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.74/0.95  thf('67', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         (~ (v1_funct_1 @ X0)
% 0.74/0.95          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.74/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.74/0.95          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.74/0.95          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.74/0.95          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.74/0.95          | (zip_tseitin_0 @ sk_D @ X0)
% 0.74/0.95          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.74/0.95          | ~ (v1_funct_1 @ sk_D))),
% 0.74/0.95      inference('sup-', [status(thm)], ['65', '66'])).
% 0.74/0.95  thf('68', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('69', plain, ((v1_funct_1 @ sk_D)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('70', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         (~ (v1_funct_1 @ X0)
% 0.74/0.95          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.74/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.74/0.95          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.74/0.95          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.74/0.95          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.74/0.95          | (zip_tseitin_0 @ sk_D @ X0))),
% 0.74/0.95      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.74/0.95  thf('71', plain,
% 0.74/0.95      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.74/0.95        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.74/0.95        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.74/0.95        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.74/0.95        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.74/0.95        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.74/0.95        | ~ (v1_funct_1 @ sk_C))),
% 0.74/0.95      inference('sup-', [status(thm)], ['64', '70'])).
% 0.74/0.95  thf(fc4_funct_1, axiom,
% 0.74/0.95    (![A:$i]:
% 0.74/0.95     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.74/0.95       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.74/0.95  thf('72', plain, (![X4 : $i]: (v2_funct_1 @ (k6_relat_1 @ X4))),
% 0.74/0.95      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.74/0.95  thf('73', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.74/0.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.74/0.95  thf('74', plain, (![X4 : $i]: (v2_funct_1 @ (k6_partfun1 @ X4))),
% 0.74/0.95      inference('demod', [status(thm)], ['72', '73'])).
% 0.74/0.95  thf('75', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('76', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('77', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('79', plain,
% 0.74/0.95      (((zip_tseitin_0 @ sk_D @ sk_C)
% 0.74/0.95        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.74/0.95        | ((sk_B) != (sk_B)))),
% 0.74/0.95      inference('demod', [status(thm)], ['71', '74', '75', '76', '77', '78'])).
% 0.74/0.95  thf('80', plain,
% 0.74/0.95      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 0.74/0.95      inference('simplify', [status(thm)], ['79'])).
% 0.74/0.95  thf('81', plain,
% 0.74/0.95      (![X41 : $i, X42 : $i]:
% 0.74/0.95         (((X41) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X41 @ X42))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.74/0.95  thf('82', plain,
% 0.74/0.95      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['80', '81'])).
% 0.74/0.95  thf('83', plain, (((sk_A) != (k1_xboole_0))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('84', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 0.74/0.95      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 0.74/0.95  thf('85', plain,
% 0.74/0.95      (![X39 : $i, X40 : $i]:
% 0.74/0.95         ((v2_funct_1 @ X40) | ~ (zip_tseitin_0 @ X40 @ X39))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.74/0.95  thf('86', plain, ((v2_funct_1 @ sk_D)),
% 0.74/0.95      inference('sup-', [status(thm)], ['84', '85'])).
% 0.74/0.95  thf('87', plain,
% 0.74/0.95      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 0.74/0.95      inference('demod', [status(thm)], ['63', '86'])).
% 0.74/0.95  thf('88', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf(t35_funct_2, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i]:
% 0.74/0.95     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.74/0.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.74/0.95       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.74/0.95         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.74/0.95           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.74/0.95             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.74/0.95  thf('89', plain,
% 0.74/0.95      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.74/0.95         (((X48) = (k1_xboole_0))
% 0.74/0.95          | ~ (v1_funct_1 @ X49)
% 0.74/0.95          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 0.74/0.95          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 0.74/0.95          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_partfun1 @ X50))
% 0.74/0.95          | ~ (v2_funct_1 @ X49)
% 0.74/0.95          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 0.74/0.95      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.74/0.95  thf('90', plain,
% 0.74/0.95      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.74/0.95        | ~ (v2_funct_1 @ sk_D)
% 0.74/0.95        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.74/0.95        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.74/0.95        | ~ (v1_funct_1 @ sk_D)
% 0.74/0.95        | ((sk_A) = (k1_xboole_0)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['88', '89'])).
% 0.74/0.95  thf('91', plain,
% 0.74/0.95      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.74/0.95      inference('sup-', [status(thm)], ['42', '43'])).
% 0.74/0.95  thf('92', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('93', plain, ((v1_funct_1 @ sk_D)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('94', plain,
% 0.74/0.95      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.74/0.95        | ~ (v2_funct_1 @ sk_D)
% 0.74/0.95        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.74/0.95        | ((sk_A) = (k1_xboole_0)))),
% 0.74/0.95      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.74/0.95  thf('95', plain, (((sk_A) != (k1_xboole_0))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('96', plain,
% 0.74/0.95      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.74/0.95        | ~ (v2_funct_1 @ sk_D)
% 0.74/0.95        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.74/0.95      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 0.74/0.95  thf('97', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.74/0.95      inference('demod', [status(thm)], ['37', '41', '44', '45', '46', '47'])).
% 0.74/0.95  thf('98', plain,
% 0.74/0.95      ((((sk_A) != (sk_A))
% 0.74/0.95        | ~ (v2_funct_1 @ sk_D)
% 0.74/0.95        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.74/0.95      inference('demod', [status(thm)], ['96', '97'])).
% 0.74/0.95  thf('99', plain,
% 0.74/0.95      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.74/0.95        | ~ (v2_funct_1 @ sk_D))),
% 0.74/0.95      inference('simplify', [status(thm)], ['98'])).
% 0.74/0.95  thf('100', plain, ((v2_funct_1 @ sk_D)),
% 0.74/0.95      inference('sup-', [status(thm)], ['84', '85'])).
% 0.74/0.95  thf('101', plain,
% 0.74/0.95      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.74/0.95      inference('demod', [status(thm)], ['99', '100'])).
% 0.74/0.95  thf(t58_funct_1, axiom,
% 0.74/0.95    (![A:$i]:
% 0.74/0.95     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.74/0.95       ( ( v2_funct_1 @ A ) =>
% 0.74/0.95         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.74/0.95             ( k1_relat_1 @ A ) ) & 
% 0.74/0.95           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.74/0.95             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.74/0.95  thf('102', plain,
% 0.74/0.95      (![X7 : $i]:
% 0.74/0.95         (~ (v2_funct_1 @ X7)
% 0.74/0.95          | ((k2_relat_1 @ (k5_relat_1 @ X7 @ (k2_funct_1 @ X7)))
% 0.74/0.95              = (k1_relat_1 @ X7))
% 0.74/0.95          | ~ (v1_funct_1 @ X7)
% 0.74/0.95          | ~ (v1_relat_1 @ X7))),
% 0.74/0.95      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.74/0.95  thf('103', plain,
% 0.74/0.95      ((((k2_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 0.74/0.95        | ~ (v1_relat_1 @ sk_D)
% 0.74/0.95        | ~ (v1_funct_1 @ sk_D)
% 0.74/0.95        | ~ (v2_funct_1 @ sk_D))),
% 0.74/0.95      inference('sup+', [status(thm)], ['101', '102'])).
% 0.74/0.95  thf(t71_relat_1, axiom,
% 0.74/0.95    (![A:$i]:
% 0.74/0.95     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.74/0.95       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.74/0.95  thf('104', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 0.74/0.95      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.74/0.95  thf('105', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.74/0.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.74/0.95  thf('106', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X1)) = (X1))),
% 0.74/0.95      inference('demod', [status(thm)], ['104', '105'])).
% 0.74/0.95  thf('107', plain, ((v1_relat_1 @ sk_D)),
% 0.74/0.95      inference('sup-', [status(thm)], ['49', '50'])).
% 0.74/0.95  thf('108', plain, ((v1_funct_1 @ sk_D)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('109', plain, ((v2_funct_1 @ sk_D)),
% 0.74/0.95      inference('sup-', [status(thm)], ['84', '85'])).
% 0.74/0.95  thf('110', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.74/0.95      inference('demod', [status(thm)], ['103', '106', '107', '108', '109'])).
% 0.74/0.95  thf('111', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 0.74/0.95      inference('demod', [status(thm)], ['87', '110'])).
% 0.74/0.95  thf('112', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.74/0.95      inference('simplify', [status(thm)], ['111'])).
% 0.74/0.95  thf(t65_funct_1, axiom,
% 0.74/0.95    (![A:$i]:
% 0.74/0.95     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.74/0.95       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.74/0.95  thf('113', plain,
% 0.74/0.95      (![X10 : $i]:
% 0.74/0.95         (~ (v2_funct_1 @ X10)
% 0.74/0.95          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.74/0.95          | ~ (v1_funct_1 @ X10)
% 0.74/0.95          | ~ (v1_relat_1 @ X10))),
% 0.74/0.95      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.74/0.95  thf('114', plain,
% 0.74/0.95      ((((k2_funct_1 @ sk_C) = (sk_D))
% 0.74/0.95        | ~ (v1_relat_1 @ sk_D)
% 0.74/0.95        | ~ (v1_funct_1 @ sk_D)
% 0.74/0.95        | ~ (v2_funct_1 @ sk_D))),
% 0.74/0.95      inference('sup+', [status(thm)], ['112', '113'])).
% 0.74/0.95  thf('115', plain, ((v1_relat_1 @ sk_D)),
% 0.74/0.95      inference('sup-', [status(thm)], ['49', '50'])).
% 0.74/0.95  thf('116', plain, ((v1_funct_1 @ sk_D)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('117', plain, ((v2_funct_1 @ sk_D)),
% 0.74/0.95      inference('sup-', [status(thm)], ['84', '85'])).
% 0.74/0.95  thf('118', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 0.74/0.95      inference('demod', [status(thm)], ['114', '115', '116', '117'])).
% 0.74/0.95  thf('119', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('120', plain, ($false),
% 0.74/0.95      inference('simplify_reflect-', [status(thm)], ['118', '119'])).
% 0.74/0.95  
% 0.74/0.95  % SZS output end Refutation
% 0.74/0.95  
% 0.74/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
