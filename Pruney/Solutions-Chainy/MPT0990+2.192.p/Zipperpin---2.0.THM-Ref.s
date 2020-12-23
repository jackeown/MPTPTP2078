%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.idGpheNmre

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:28 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  211 (4847 expanded)
%              Number of leaves         :   45 (1403 expanded)
%              Depth                    :   28
%              Number of atoms          : 2060 (136349 expanded)
%              Number of equality atoms :  160 (9187 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( X14 = X17 )
      | ~ ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('24',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('25',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

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
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X9 @ X10 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('27',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X9 @ X10 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

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
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( r2_relset_1 @ X34 @ X34 @ ( k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36 ) @ ( k6_partfun1 @ X34 ) )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
        = X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

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
    inference(demod,[status(thm)],['37','38','41','42','43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('54',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','45','50','51','56','57','62'])).

thf('64',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('66',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('67',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
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

thf('69',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( zip_tseitin_0 @ X41 @ X44 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X45 @ X42 @ X42 @ X43 @ X44 @ X41 ) )
      | ( zip_tseitin_1 @ X43 @ X42 )
      | ( ( k2_relset_1 @ X45 @ X42 @ X44 )
       != X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('70',plain,(
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
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
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
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
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

thf('76',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('77',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['74','77','78','79','80','81'])).

thf('83',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X39: $i,X40: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('85',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v2_funct_1 @ X38 )
      | ~ ( zip_tseitin_0 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('89',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','89'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('91',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('92',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('93',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
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

thf('95',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X46 ) ) )
      | ( ( k5_relat_1 @ X47 @ ( k2_funct_1 @ X47 ) )
        = ( k6_partfun1 @ X48 ) )
      | ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relset_1 @ X48 @ X46 @ X47 )
       != X46 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('96',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','38','41','42','43','44'])).

thf('99',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','99','100','101'])).

thf('103',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['87','88'])).

thf('107',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['93','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('110',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['87','88'])).

thf('112',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('113',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('114',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('115',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('118',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['90','118'])).

thf('120',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('122',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X9 @ X10 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['120','124'])).

thf('126',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('127',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['54','55'])).

thf('128',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('129',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['87','88'])).

thf('131',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['119'])).

thf('132',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('133',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['119'])).

thf('134',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['119'])).

thf('136',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','38','41','42','43','44'])).

thf('138',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['119'])).

thf('139',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X46 ) ) )
      | ( ( k5_relat_1 @ X47 @ ( k2_funct_1 @ X47 ) )
        = ( k6_partfun1 @ X48 ) )
      | ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relset_1 @ X48 @ X46 @ X47 )
       != X46 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('142',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['142','143','144','145','146'])).

thf('148',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['139','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['151','152','153','154'])).

thf('156',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('157',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('159',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['119'])).

thf('161',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['125','126','127','128','129','130','131','132','133','134','135','136','137','138','159','160'])).

thf('162',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['162','163'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.idGpheNmre
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:03:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.01/1.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.01/1.20  % Solved by: fo/fo7.sh
% 1.01/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.20  % done 1262 iterations in 0.741s
% 1.01/1.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.01/1.20  % SZS output start Refutation
% 1.01/1.20  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.01/1.20  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.01/1.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.01/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.01/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.01/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.20  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.01/1.20  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.01/1.20  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.01/1.20  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.01/1.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.01/1.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.01/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.01/1.20  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.01/1.20  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.01/1.20  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.01/1.20  thf(sk_D_type, type, sk_D: $i).
% 1.01/1.20  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.01/1.20  thf(sk_C_type, type, sk_C: $i).
% 1.01/1.20  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.01/1.20  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.01/1.20  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.01/1.20  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.01/1.20  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.01/1.20  thf(t36_funct_2, conjecture,
% 1.01/1.20    (![A:$i,B:$i,C:$i]:
% 1.01/1.20     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.01/1.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.01/1.20       ( ![D:$i]:
% 1.01/1.20         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.01/1.20             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.01/1.20           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.01/1.20               ( r2_relset_1 @
% 1.01/1.20                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.01/1.20                 ( k6_partfun1 @ A ) ) & 
% 1.01/1.20               ( v2_funct_1 @ C ) ) =>
% 1.01/1.20             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.01/1.20               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.01/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.01/1.20    (~( ![A:$i,B:$i,C:$i]:
% 1.01/1.20        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.01/1.20            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.01/1.20          ( ![D:$i]:
% 1.01/1.20            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.01/1.20                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.01/1.20              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.01/1.20                  ( r2_relset_1 @
% 1.01/1.20                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.01/1.20                    ( k6_partfun1 @ A ) ) & 
% 1.01/1.20                  ( v2_funct_1 @ C ) ) =>
% 1.01/1.20                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.01/1.20                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.01/1.20    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.01/1.20  thf('0', plain,
% 1.01/1.20      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.01/1.20        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.01/1.20        (k6_partfun1 @ sk_A))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('1', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('2', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(redefinition_k1_partfun1, axiom,
% 1.01/1.20    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.01/1.20     ( ( ( v1_funct_1 @ E ) & 
% 1.01/1.20         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.01/1.20         ( v1_funct_1 @ F ) & 
% 1.01/1.20         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.01/1.20       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.01/1.20  thf('3', plain,
% 1.01/1.20      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.01/1.20          | ~ (v1_funct_1 @ X26)
% 1.01/1.20          | ~ (v1_funct_1 @ X29)
% 1.01/1.20          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.01/1.20          | ((k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 1.01/1.20              = (k5_relat_1 @ X26 @ X29)))),
% 1.01/1.20      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.01/1.20  thf('4', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.01/1.20            = (k5_relat_1 @ sk_C @ X0))
% 1.01/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.01/1.20          | ~ (v1_funct_1 @ X0)
% 1.01/1.20          | ~ (v1_funct_1 @ sk_C))),
% 1.01/1.20      inference('sup-', [status(thm)], ['2', '3'])).
% 1.01/1.20  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('6', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.01/1.20            = (k5_relat_1 @ sk_C @ X0))
% 1.01/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.01/1.20          | ~ (v1_funct_1 @ X0))),
% 1.01/1.20      inference('demod', [status(thm)], ['4', '5'])).
% 1.01/1.20  thf('7', plain,
% 1.01/1.20      ((~ (v1_funct_1 @ sk_D)
% 1.01/1.20        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.01/1.20            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['1', '6'])).
% 1.01/1.20  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('9', plain,
% 1.01/1.20      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.01/1.20         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['7', '8'])).
% 1.01/1.20  thf('10', plain,
% 1.01/1.20      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.01/1.20        (k6_partfun1 @ sk_A))),
% 1.01/1.20      inference('demod', [status(thm)], ['0', '9'])).
% 1.01/1.20  thf('11', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('12', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(dt_k1_partfun1, axiom,
% 1.01/1.20    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.01/1.20     ( ( ( v1_funct_1 @ E ) & 
% 1.01/1.20         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.01/1.20         ( v1_funct_1 @ F ) & 
% 1.01/1.20         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.01/1.20       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.01/1.20         ( m1_subset_1 @
% 1.01/1.20           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.01/1.20           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.01/1.20  thf('13', plain,
% 1.01/1.20      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.01/1.20          | ~ (v1_funct_1 @ X18)
% 1.01/1.20          | ~ (v1_funct_1 @ X21)
% 1.01/1.20          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.01/1.20          | (m1_subset_1 @ (k1_partfun1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21) @ 
% 1.01/1.20             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X23))))),
% 1.01/1.20      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.01/1.20  thf('14', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.01/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.01/1.20          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.01/1.20          | ~ (v1_funct_1 @ X1)
% 1.01/1.20          | ~ (v1_funct_1 @ sk_C))),
% 1.01/1.20      inference('sup-', [status(thm)], ['12', '13'])).
% 1.01/1.20  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('16', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.01/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.01/1.20          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.01/1.20          | ~ (v1_funct_1 @ X1))),
% 1.01/1.20      inference('demod', [status(thm)], ['14', '15'])).
% 1.01/1.20  thf('17', plain,
% 1.01/1.20      ((~ (v1_funct_1 @ sk_D)
% 1.01/1.20        | (m1_subset_1 @ 
% 1.01/1.20           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.01/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['11', '16'])).
% 1.01/1.20  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('19', plain,
% 1.01/1.20      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.01/1.20         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['7', '8'])).
% 1.01/1.20  thf('20', plain,
% 1.01/1.20      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.01/1.20        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.01/1.20      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.01/1.20  thf(redefinition_r2_relset_1, axiom,
% 1.01/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.01/1.20     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.01/1.20         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.01/1.20       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.01/1.20  thf('21', plain,
% 1.01/1.20      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.01/1.20          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.01/1.20          | ((X14) = (X17))
% 1.01/1.20          | ~ (r2_relset_1 @ X15 @ X16 @ X14 @ X17))),
% 1.01/1.20      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.01/1.20  thf('22', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.01/1.20          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.01/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['20', '21'])).
% 1.01/1.20  thf('23', plain,
% 1.01/1.20      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.01/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.01/1.20        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['10', '22'])).
% 1.01/1.20  thf(dt_k6_partfun1, axiom,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( m1_subset_1 @
% 1.01/1.20         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.01/1.20       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.01/1.20  thf('24', plain,
% 1.01/1.20      (![X25 : $i]:
% 1.01/1.20         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 1.01/1.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 1.01/1.20      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.01/1.20  thf('25', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.01/1.20      inference('demod', [status(thm)], ['23', '24'])).
% 1.01/1.20  thf(t64_funct_1, axiom,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.01/1.20       ( ![B:$i]:
% 1.01/1.20         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.01/1.20           ( ( ( v2_funct_1 @ A ) & 
% 1.01/1.20               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.01/1.20               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.01/1.20             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.01/1.20  thf('26', plain,
% 1.01/1.20      (![X9 : $i, X10 : $i]:
% 1.01/1.20         (~ (v1_relat_1 @ X9)
% 1.01/1.20          | ~ (v1_funct_1 @ X9)
% 1.01/1.20          | ((X9) = (k2_funct_1 @ X10))
% 1.01/1.20          | ((k5_relat_1 @ X9 @ X10) != (k6_relat_1 @ (k2_relat_1 @ X10)))
% 1.01/1.20          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 1.01/1.20          | ~ (v2_funct_1 @ X10)
% 1.01/1.20          | ~ (v1_funct_1 @ X10)
% 1.01/1.20          | ~ (v1_relat_1 @ X10))),
% 1.01/1.20      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.01/1.20  thf(redefinition_k6_partfun1, axiom,
% 1.01/1.20    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.01/1.20  thf('27', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.01/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.01/1.20  thf('28', plain,
% 1.01/1.20      (![X9 : $i, X10 : $i]:
% 1.01/1.20         (~ (v1_relat_1 @ X9)
% 1.01/1.20          | ~ (v1_funct_1 @ X9)
% 1.01/1.20          | ((X9) = (k2_funct_1 @ X10))
% 1.01/1.20          | ((k5_relat_1 @ X9 @ X10) != (k6_partfun1 @ (k2_relat_1 @ X10)))
% 1.01/1.20          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 1.01/1.20          | ~ (v2_funct_1 @ X10)
% 1.01/1.20          | ~ (v1_funct_1 @ X10)
% 1.01/1.20          | ~ (v1_relat_1 @ X10))),
% 1.01/1.20      inference('demod', [status(thm)], ['26', '27'])).
% 1.01/1.20  thf('29', plain,
% 1.01/1.20      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.01/1.20        | ~ (v1_relat_1 @ sk_D)
% 1.01/1.20        | ~ (v1_funct_1 @ sk_D)
% 1.01/1.20        | ~ (v2_funct_1 @ sk_D)
% 1.01/1.20        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.01/1.20        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.01/1.20        | ~ (v1_funct_1 @ sk_C)
% 1.01/1.20        | ~ (v1_relat_1 @ sk_C))),
% 1.01/1.20      inference('sup-', [status(thm)], ['25', '28'])).
% 1.01/1.20  thf('30', plain,
% 1.01/1.20      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.01/1.20         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['7', '8'])).
% 1.01/1.20  thf('31', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(t24_funct_2, axiom,
% 1.01/1.20    (![A:$i,B:$i,C:$i]:
% 1.01/1.20     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.01/1.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.01/1.20       ( ![D:$i]:
% 1.01/1.20         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.01/1.20             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.01/1.20           ( ( r2_relset_1 @
% 1.01/1.20               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.01/1.20               ( k6_partfun1 @ B ) ) =>
% 1.01/1.20             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.01/1.20  thf('32', plain,
% 1.01/1.20      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.01/1.20         (~ (v1_funct_1 @ X33)
% 1.01/1.20          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 1.01/1.20          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.01/1.20          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 1.01/1.20               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 1.01/1.20               (k6_partfun1 @ X34))
% 1.01/1.20          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 1.01/1.20          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 1.01/1.20          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 1.01/1.20          | ~ (v1_funct_1 @ X36))),
% 1.01/1.20      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.01/1.20  thf('33', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (v1_funct_1 @ X0)
% 1.01/1.20          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.01/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.01/1.20          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.01/1.20          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.01/1.20               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.01/1.20               (k6_partfun1 @ sk_A))
% 1.01/1.20          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.01/1.20          | ~ (v1_funct_1 @ sk_C))),
% 1.01/1.20      inference('sup-', [status(thm)], ['31', '32'])).
% 1.01/1.20  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('36', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (v1_funct_1 @ X0)
% 1.01/1.20          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.01/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.01/1.20          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.01/1.20          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.01/1.20               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.01/1.20               (k6_partfun1 @ sk_A)))),
% 1.01/1.20      inference('demod', [status(thm)], ['33', '34', '35'])).
% 1.01/1.20  thf('37', plain,
% 1.01/1.20      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.01/1.20           (k6_partfun1 @ sk_A))
% 1.01/1.20        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.01/1.20        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.01/1.20        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.01/1.20        | ~ (v1_funct_1 @ sk_D))),
% 1.01/1.20      inference('sup-', [status(thm)], ['30', '36'])).
% 1.01/1.20  thf('38', plain,
% 1.01/1.20      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.01/1.20        (k6_partfun1 @ sk_A))),
% 1.01/1.20      inference('demod', [status(thm)], ['0', '9'])).
% 1.01/1.20  thf('39', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(redefinition_k2_relset_1, axiom,
% 1.01/1.20    (![A:$i,B:$i,C:$i]:
% 1.01/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.01/1.20       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.01/1.20  thf('40', plain,
% 1.01/1.20      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.01/1.20         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.01/1.20          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.01/1.20      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.01/1.20  thf('41', plain,
% 1.01/1.20      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.01/1.20      inference('sup-', [status(thm)], ['39', '40'])).
% 1.01/1.20  thf('42', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('43', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('45', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.01/1.20      inference('demod', [status(thm)], ['37', '38', '41', '42', '43', '44'])).
% 1.01/1.20  thf('46', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(cc2_relat_1, axiom,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( v1_relat_1 @ A ) =>
% 1.01/1.20       ( ![B:$i]:
% 1.01/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.01/1.20  thf('47', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.01/1.20          | (v1_relat_1 @ X0)
% 1.01/1.20          | ~ (v1_relat_1 @ X1))),
% 1.01/1.20      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.01/1.20  thf('48', plain,
% 1.01/1.20      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.01/1.20      inference('sup-', [status(thm)], ['46', '47'])).
% 1.01/1.20  thf(fc6_relat_1, axiom,
% 1.01/1.20    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.01/1.20  thf('49', plain,
% 1.01/1.20      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.01/1.20      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.01/1.20  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 1.01/1.20      inference('demod', [status(thm)], ['48', '49'])).
% 1.01/1.20  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('52', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('53', plain,
% 1.01/1.20      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.01/1.20         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.01/1.20          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.01/1.20      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.01/1.20  thf('54', plain,
% 1.01/1.20      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.01/1.20      inference('sup-', [status(thm)], ['52', '53'])).
% 1.01/1.20  thf('55', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('56', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.01/1.20      inference('sup+', [status(thm)], ['54', '55'])).
% 1.01/1.20  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('58', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('59', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.01/1.20          | (v1_relat_1 @ X0)
% 1.01/1.20          | ~ (v1_relat_1 @ X1))),
% 1.01/1.20      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.01/1.20  thf('60', plain,
% 1.01/1.20      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.01/1.20      inference('sup-', [status(thm)], ['58', '59'])).
% 1.01/1.20  thf('61', plain,
% 1.01/1.20      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.01/1.20      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.01/1.20  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 1.01/1.20      inference('demod', [status(thm)], ['60', '61'])).
% 1.01/1.20  thf('63', plain,
% 1.01/1.20      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 1.01/1.20        | ~ (v2_funct_1 @ sk_D)
% 1.01/1.20        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.01/1.20        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.01/1.20      inference('demod', [status(thm)],
% 1.01/1.20                ['29', '45', '50', '51', '56', '57', '62'])).
% 1.01/1.20  thf('64', plain,
% 1.01/1.20      ((((sk_C) = (k2_funct_1 @ sk_D))
% 1.01/1.20        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.01/1.20        | ~ (v2_funct_1 @ sk_D))),
% 1.01/1.20      inference('simplify', [status(thm)], ['63'])).
% 1.01/1.20  thf('65', plain,
% 1.01/1.20      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.01/1.20         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['7', '8'])).
% 1.01/1.20  thf('66', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.01/1.20      inference('demod', [status(thm)], ['23', '24'])).
% 1.01/1.20  thf('67', plain,
% 1.01/1.20      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.01/1.20         = (k6_partfun1 @ sk_A))),
% 1.01/1.20      inference('demod', [status(thm)], ['65', '66'])).
% 1.01/1.20  thf('68', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(t30_funct_2, axiom,
% 1.01/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.01/1.20     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.01/1.20         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.01/1.20       ( ![E:$i]:
% 1.01/1.20         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.01/1.20             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.01/1.20           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.01/1.20               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.01/1.20             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.01/1.20               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.01/1.20  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.01/1.20  thf(zf_stmt_2, axiom,
% 1.01/1.20    (![C:$i,B:$i]:
% 1.01/1.20     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.01/1.20       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.01/1.20  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.01/1.20  thf(zf_stmt_4, axiom,
% 1.01/1.20    (![E:$i,D:$i]:
% 1.01/1.20     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.01/1.20  thf(zf_stmt_5, axiom,
% 1.01/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.01/1.20     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.01/1.20         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.01/1.20       ( ![E:$i]:
% 1.01/1.20         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.01/1.20             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.01/1.20           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.01/1.20               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.01/1.20             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.01/1.20  thf('69', plain,
% 1.01/1.20      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 1.01/1.20         (~ (v1_funct_1 @ X41)
% 1.01/1.20          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 1.01/1.20          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.01/1.20          | (zip_tseitin_0 @ X41 @ X44)
% 1.01/1.20          | ~ (v2_funct_1 @ (k1_partfun1 @ X45 @ X42 @ X42 @ X43 @ X44 @ X41))
% 1.01/1.20          | (zip_tseitin_1 @ X43 @ X42)
% 1.01/1.20          | ((k2_relset_1 @ X45 @ X42 @ X44) != (X42))
% 1.01/1.20          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X42)))
% 1.01/1.20          | ~ (v1_funct_2 @ X44 @ X45 @ X42)
% 1.01/1.20          | ~ (v1_funct_1 @ X44))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.01/1.20  thf('70', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         (~ (v1_funct_1 @ X0)
% 1.01/1.20          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.01/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.01/1.20          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.01/1.20          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.01/1.20          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.01/1.20          | (zip_tseitin_0 @ sk_D @ X0)
% 1.01/1.20          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.01/1.20          | ~ (v1_funct_1 @ sk_D))),
% 1.01/1.20      inference('sup-', [status(thm)], ['68', '69'])).
% 1.01/1.20  thf('71', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('73', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         (~ (v1_funct_1 @ X0)
% 1.01/1.20          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.01/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.01/1.20          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.01/1.20          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.01/1.20          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.01/1.20          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.01/1.20      inference('demod', [status(thm)], ['70', '71', '72'])).
% 1.01/1.20  thf('74', plain,
% 1.01/1.20      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.01/1.20        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.01/1.20        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.01/1.20        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.01/1.20        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.01/1.20        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.01/1.20        | ~ (v1_funct_1 @ sk_C))),
% 1.01/1.20      inference('sup-', [status(thm)], ['67', '73'])).
% 1.01/1.20  thf(fc4_funct_1, axiom,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.01/1.20       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.01/1.20  thf('75', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 1.01/1.20      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.01/1.20  thf('76', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.01/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.01/1.20  thf('77', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 1.01/1.20      inference('demod', [status(thm)], ['75', '76'])).
% 1.01/1.20  thf('78', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('79', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('80', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('82', plain,
% 1.01/1.20      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.01/1.20        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.01/1.20        | ((sk_B) != (sk_B)))),
% 1.01/1.20      inference('demod', [status(thm)], ['74', '77', '78', '79', '80', '81'])).
% 1.01/1.20  thf('83', plain,
% 1.01/1.20      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.01/1.20      inference('simplify', [status(thm)], ['82'])).
% 1.01/1.20  thf('84', plain,
% 1.01/1.20      (![X39 : $i, X40 : $i]:
% 1.01/1.20         (((X39) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X39 @ X40))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.01/1.20  thf('85', plain,
% 1.01/1.20      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['83', '84'])).
% 1.01/1.20  thf('86', plain, (((sk_A) != (k1_xboole_0))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('87', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.01/1.20      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 1.01/1.20  thf('88', plain,
% 1.01/1.20      (![X37 : $i, X38 : $i]:
% 1.01/1.20         ((v2_funct_1 @ X38) | ~ (zip_tseitin_0 @ X38 @ X37))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.01/1.20  thf('89', plain, ((v2_funct_1 @ sk_D)),
% 1.01/1.20      inference('sup-', [status(thm)], ['87', '88'])).
% 1.01/1.20  thf('90', plain,
% 1.01/1.20      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 1.01/1.20      inference('demod', [status(thm)], ['64', '89'])).
% 1.01/1.20  thf(t61_funct_1, axiom,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.01/1.20       ( ( v2_funct_1 @ A ) =>
% 1.01/1.20         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.01/1.20             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.01/1.20           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.01/1.20             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.01/1.20  thf('91', plain,
% 1.01/1.20      (![X8 : $i]:
% 1.01/1.20         (~ (v2_funct_1 @ X8)
% 1.01/1.20          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 1.01/1.20              = (k6_relat_1 @ (k1_relat_1 @ X8)))
% 1.01/1.20          | ~ (v1_funct_1 @ X8)
% 1.01/1.20          | ~ (v1_relat_1 @ X8))),
% 1.01/1.20      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.01/1.20  thf('92', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.01/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.01/1.20  thf('93', plain,
% 1.01/1.20      (![X8 : $i]:
% 1.01/1.20         (~ (v2_funct_1 @ X8)
% 1.01/1.20          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 1.01/1.20              = (k6_partfun1 @ (k1_relat_1 @ X8)))
% 1.01/1.20          | ~ (v1_funct_1 @ X8)
% 1.01/1.20          | ~ (v1_relat_1 @ X8))),
% 1.01/1.20      inference('demod', [status(thm)], ['91', '92'])).
% 1.01/1.20  thf('94', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(t35_funct_2, axiom,
% 1.01/1.20    (![A:$i,B:$i,C:$i]:
% 1.01/1.20     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.01/1.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.01/1.20       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.01/1.20         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.01/1.20           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.01/1.20             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.01/1.20  thf('95', plain,
% 1.01/1.20      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.01/1.20         (((X46) = (k1_xboole_0))
% 1.01/1.20          | ~ (v1_funct_1 @ X47)
% 1.01/1.20          | ~ (v1_funct_2 @ X47 @ X48 @ X46)
% 1.01/1.20          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X46)))
% 1.01/1.20          | ((k5_relat_1 @ X47 @ (k2_funct_1 @ X47)) = (k6_partfun1 @ X48))
% 1.01/1.20          | ~ (v2_funct_1 @ X47)
% 1.01/1.20          | ((k2_relset_1 @ X48 @ X46 @ X47) != (X46)))),
% 1.01/1.20      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.01/1.20  thf('96', plain,
% 1.01/1.20      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.01/1.20        | ~ (v2_funct_1 @ sk_D)
% 1.01/1.20        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.01/1.20        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.01/1.20        | ~ (v1_funct_1 @ sk_D)
% 1.01/1.20        | ((sk_A) = (k1_xboole_0)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['94', '95'])).
% 1.01/1.20  thf('97', plain,
% 1.01/1.20      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.01/1.20      inference('sup-', [status(thm)], ['39', '40'])).
% 1.01/1.20  thf('98', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.01/1.20      inference('demod', [status(thm)], ['37', '38', '41', '42', '43', '44'])).
% 1.01/1.20  thf('99', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 1.01/1.20      inference('demod', [status(thm)], ['97', '98'])).
% 1.01/1.20  thf('100', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('101', plain, ((v1_funct_1 @ sk_D)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('102', plain,
% 1.01/1.20      ((((sk_A) != (sk_A))
% 1.01/1.20        | ~ (v2_funct_1 @ sk_D)
% 1.01/1.20        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.01/1.20        | ((sk_A) = (k1_xboole_0)))),
% 1.01/1.20      inference('demod', [status(thm)], ['96', '99', '100', '101'])).
% 1.01/1.20  thf('103', plain,
% 1.01/1.20      ((((sk_A) = (k1_xboole_0))
% 1.01/1.20        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.01/1.20        | ~ (v2_funct_1 @ sk_D))),
% 1.01/1.20      inference('simplify', [status(thm)], ['102'])).
% 1.01/1.20  thf('104', plain, (((sk_A) != (k1_xboole_0))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('105', plain,
% 1.01/1.20      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.01/1.20        | ~ (v2_funct_1 @ sk_D))),
% 1.01/1.20      inference('simplify_reflect-', [status(thm)], ['103', '104'])).
% 1.01/1.20  thf('106', plain, ((v2_funct_1 @ sk_D)),
% 1.01/1.20      inference('sup-', [status(thm)], ['87', '88'])).
% 1.01/1.20  thf('107', plain,
% 1.01/1.20      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.01/1.20      inference('demod', [status(thm)], ['105', '106'])).
% 1.01/1.20  thf('108', plain,
% 1.01/1.20      ((((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.01/1.20        | ~ (v1_relat_1 @ sk_D)
% 1.01/1.20        | ~ (v1_funct_1 @ sk_D)
% 1.01/1.20        | ~ (v2_funct_1 @ sk_D))),
% 1.01/1.20      inference('sup+', [status(thm)], ['93', '107'])).
% 1.01/1.20  thf('109', plain, ((v1_relat_1 @ sk_D)),
% 1.01/1.20      inference('demod', [status(thm)], ['48', '49'])).
% 1.01/1.20  thf('110', plain, ((v1_funct_1 @ sk_D)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('111', plain, ((v2_funct_1 @ sk_D)),
% 1.01/1.20      inference('sup-', [status(thm)], ['87', '88'])).
% 1.01/1.20  thf('112', plain,
% 1.01/1.20      (((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.01/1.20      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 1.01/1.20  thf(t71_relat_1, axiom,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.01/1.20       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.01/1.20  thf('113', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 1.01/1.20      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.01/1.20  thf('114', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.01/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.01/1.20  thf('115', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 1.01/1.20      inference('demod', [status(thm)], ['113', '114'])).
% 1.01/1.20  thf('116', plain,
% 1.01/1.20      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 1.01/1.20      inference('sup+', [status(thm)], ['112', '115'])).
% 1.01/1.20  thf('117', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 1.01/1.20      inference('demod', [status(thm)], ['113', '114'])).
% 1.01/1.20  thf('118', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['116', '117'])).
% 1.01/1.20  thf('119', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 1.01/1.20      inference('demod', [status(thm)], ['90', '118'])).
% 1.01/1.20  thf('120', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.01/1.20      inference('simplify', [status(thm)], ['119'])).
% 1.01/1.20  thf('121', plain,
% 1.01/1.20      (![X8 : $i]:
% 1.01/1.20         (~ (v2_funct_1 @ X8)
% 1.01/1.20          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 1.01/1.20              = (k6_partfun1 @ (k1_relat_1 @ X8)))
% 1.01/1.20          | ~ (v1_funct_1 @ X8)
% 1.01/1.20          | ~ (v1_relat_1 @ X8))),
% 1.01/1.20      inference('demod', [status(thm)], ['91', '92'])).
% 1.01/1.20  thf('122', plain,
% 1.01/1.20      (![X9 : $i, X10 : $i]:
% 1.01/1.20         (~ (v1_relat_1 @ X9)
% 1.01/1.20          | ~ (v1_funct_1 @ X9)
% 1.01/1.20          | ((X9) = (k2_funct_1 @ X10))
% 1.01/1.20          | ((k5_relat_1 @ X9 @ X10) != (k6_partfun1 @ (k2_relat_1 @ X10)))
% 1.01/1.20          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 1.01/1.20          | ~ (v2_funct_1 @ X10)
% 1.01/1.20          | ~ (v1_funct_1 @ X10)
% 1.01/1.20          | ~ (v1_relat_1 @ X10))),
% 1.01/1.20      inference('demod', [status(thm)], ['26', '27'])).
% 1.01/1.20  thf('123', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.01/1.20            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.01/1.20          | ~ (v1_relat_1 @ X0)
% 1.01/1.20          | ~ (v1_funct_1 @ X0)
% 1.01/1.20          | ~ (v2_funct_1 @ X0)
% 1.01/1.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.01/1.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.01/1.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.01/1.20          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.01/1.20          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.01/1.20          | ~ (v1_funct_1 @ X0)
% 1.01/1.20          | ~ (v1_relat_1 @ X0))),
% 1.01/1.20      inference('sup-', [status(thm)], ['121', '122'])).
% 1.01/1.20  thf('124', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.01/1.20          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.01/1.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.01/1.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.01/1.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.01/1.20          | ~ (v2_funct_1 @ X0)
% 1.01/1.20          | ~ (v1_funct_1 @ X0)
% 1.01/1.20          | ~ (v1_relat_1 @ X0)
% 1.01/1.20          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.01/1.20              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.01/1.20      inference('simplify', [status(thm)], ['123'])).
% 1.01/1.20  thf('125', plain,
% 1.01/1.20      ((((k6_partfun1 @ (k1_relat_1 @ sk_D))
% 1.01/1.20          != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.01/1.20        | ~ (v1_relat_1 @ sk_D)
% 1.01/1.20        | ~ (v1_funct_1 @ sk_D)
% 1.01/1.20        | ~ (v2_funct_1 @ sk_D)
% 1.01/1.20        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 1.01/1.20        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 1.01/1.20        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 1.01/1.20        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 1.01/1.20        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['120', '124'])).
% 1.01/1.20  thf('126', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['116', '117'])).
% 1.01/1.20  thf('127', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.01/1.20      inference('sup+', [status(thm)], ['54', '55'])).
% 1.01/1.20  thf('128', plain, ((v1_relat_1 @ sk_D)),
% 1.01/1.20      inference('demod', [status(thm)], ['48', '49'])).
% 1.01/1.20  thf('129', plain, ((v1_funct_1 @ sk_D)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('130', plain, ((v2_funct_1 @ sk_D)),
% 1.01/1.20      inference('sup-', [status(thm)], ['87', '88'])).
% 1.01/1.20  thf('131', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.01/1.20      inference('simplify', [status(thm)], ['119'])).
% 1.01/1.20  thf('132', plain, ((v1_relat_1 @ sk_C)),
% 1.01/1.20      inference('demod', [status(thm)], ['60', '61'])).
% 1.01/1.20  thf('133', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.01/1.20      inference('simplify', [status(thm)], ['119'])).
% 1.01/1.20  thf('134', plain, ((v1_funct_1 @ sk_C)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('135', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.01/1.20      inference('simplify', [status(thm)], ['119'])).
% 1.01/1.20  thf('136', plain, ((v2_funct_1 @ sk_C)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('137', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.01/1.20      inference('demod', [status(thm)], ['37', '38', '41', '42', '43', '44'])).
% 1.01/1.20  thf('138', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.01/1.20      inference('simplify', [status(thm)], ['119'])).
% 1.01/1.20  thf('139', plain,
% 1.01/1.20      (![X8 : $i]:
% 1.01/1.20         (~ (v2_funct_1 @ X8)
% 1.01/1.20          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 1.01/1.20              = (k6_partfun1 @ (k1_relat_1 @ X8)))
% 1.01/1.20          | ~ (v1_funct_1 @ X8)
% 1.01/1.20          | ~ (v1_relat_1 @ X8))),
% 1.01/1.20      inference('demod', [status(thm)], ['91', '92'])).
% 1.01/1.20  thf('140', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('141', plain,
% 1.01/1.20      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.01/1.20         (((X46) = (k1_xboole_0))
% 1.01/1.20          | ~ (v1_funct_1 @ X47)
% 1.01/1.20          | ~ (v1_funct_2 @ X47 @ X48 @ X46)
% 1.01/1.20          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X46)))
% 1.01/1.20          | ((k5_relat_1 @ X47 @ (k2_funct_1 @ X47)) = (k6_partfun1 @ X48))
% 1.01/1.20          | ~ (v2_funct_1 @ X47)
% 1.01/1.20          | ((k2_relset_1 @ X48 @ X46 @ X47) != (X46)))),
% 1.01/1.20      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.01/1.20  thf('142', plain,
% 1.01/1.20      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.01/1.20        | ~ (v2_funct_1 @ sk_C)
% 1.01/1.20        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.01/1.20        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.01/1.20        | ~ (v1_funct_1 @ sk_C)
% 1.01/1.20        | ((sk_B) = (k1_xboole_0)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['140', '141'])).
% 1.01/1.20  thf('143', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('145', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('147', plain,
% 1.01/1.20      ((((sk_B) != (sk_B))
% 1.01/1.20        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.01/1.20        | ((sk_B) = (k1_xboole_0)))),
% 1.01/1.20      inference('demod', [status(thm)], ['142', '143', '144', '145', '146'])).
% 1.01/1.20  thf('148', plain,
% 1.01/1.20      ((((sk_B) = (k1_xboole_0))
% 1.01/1.20        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 1.01/1.20      inference('simplify', [status(thm)], ['147'])).
% 1.01/1.20  thf('149', plain, (((sk_B) != (k1_xboole_0))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('150', plain,
% 1.01/1.20      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.01/1.20      inference('simplify_reflect-', [status(thm)], ['148', '149'])).
% 1.01/1.20  thf('151', plain,
% 1.01/1.20      ((((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.01/1.20        | ~ (v1_relat_1 @ sk_C)
% 1.01/1.20        | ~ (v1_funct_1 @ sk_C)
% 1.01/1.20        | ~ (v2_funct_1 @ sk_C))),
% 1.01/1.20      inference('sup+', [status(thm)], ['139', '150'])).
% 1.01/1.20  thf('152', plain, ((v1_relat_1 @ sk_C)),
% 1.01/1.20      inference('demod', [status(thm)], ['60', '61'])).
% 1.01/1.20  thf('153', plain, ((v1_funct_1 @ sk_C)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('154', plain, ((v2_funct_1 @ sk_C)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('155', plain,
% 1.01/1.20      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.01/1.20      inference('demod', [status(thm)], ['151', '152', '153', '154'])).
% 1.01/1.20  thf('156', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 1.01/1.20      inference('demod', [status(thm)], ['113', '114'])).
% 1.01/1.20  thf('157', plain,
% 1.01/1.20      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 1.01/1.20      inference('sup+', [status(thm)], ['155', '156'])).
% 1.01/1.20  thf('158', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 1.01/1.20      inference('demod', [status(thm)], ['113', '114'])).
% 1.01/1.20  thf('159', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.01/1.20      inference('demod', [status(thm)], ['157', '158'])).
% 1.01/1.20  thf('160', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.01/1.20      inference('simplify', [status(thm)], ['119'])).
% 1.01/1.20  thf('161', plain,
% 1.01/1.20      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 1.01/1.20        | ((sk_A) != (sk_A))
% 1.01/1.20        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.01/1.20      inference('demod', [status(thm)],
% 1.01/1.20                ['125', '126', '127', '128', '129', '130', '131', '132', 
% 1.01/1.20                 '133', '134', '135', '136', '137', '138', '159', '160'])).
% 1.01/1.20  thf('162', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.01/1.20      inference('simplify', [status(thm)], ['161'])).
% 1.01/1.20  thf('163', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('164', plain, ($false),
% 1.01/1.20      inference('simplify_reflect-', [status(thm)], ['162', '163'])).
% 1.01/1.20  
% 1.01/1.20  % SZS output end Refutation
% 1.01/1.20  
% 1.01/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
