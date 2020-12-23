%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lrJyg8vRVa

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:29 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  240 (5800 expanded)
%              Number of leaves         :   45 (1770 expanded)
%              Depth                    :   27
%              Number of atoms          : 2367 (130168 expanded)
%              Number of equality atoms :  174 (8432 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X25 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
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
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
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

thf('27',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X10 @ X11 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X10 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('39',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','48','53','54','59','60','65'])).

thf('67',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('69',plain,(
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

thf('70',plain,(
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

thf('71',plain,(
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
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('85',plain,(
    v1_funct_1 @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('86',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('87',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('88',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('89',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) @ X6 )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('90',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('91',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X6 ) ) @ X6 )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','97'])).

thf(t53_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('99',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X8 @ X7 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('100',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('101',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X8 @ X7 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('104',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('105',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','103','104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    v2_funct_1 @ ( k6_partfun1 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','107'])).

thf('109',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['75','108','109','110','111','112'])).

thf('114',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X39: $i,X40: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('116',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v2_funct_1 @ X38 )
      | ~ ( zip_tseitin_0 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('120',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['67','120'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('122',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('123',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('124',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
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

thf('126',plain,(
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

thf('127',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('129',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','41','44','45','46','47'])).

thf('135',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['118','119'])).

thf('138',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['124','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('141',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['118','119'])).

thf('143',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('145',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('147',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['121','147'])).

thf('149',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('151',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X10 @ X11 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X10 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('152',plain,(
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
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
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
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,
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
    inference('sup-',[status(thm)],['149','153'])).

thf('155',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('156',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('157',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('158',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['118','119'])).

thf('160',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['148'])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('162',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['148'])).

thf('163',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['148'])).

thf('165',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','41','44','45','46','47'])).

thf('167',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['148'])).

thf('168',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('169',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
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

thf('171',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['171','172','173','174','175'])).

thf('177',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['168','179'])).

thf('181',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('182',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['180','181','182','183'])).

thf('185',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('186',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('188',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['148'])).

thf('190',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['154','155','156','157','158','159','160','161','162','163','164','165','166','167','188','189'])).

thf('191',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['191','192'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lrJyg8vRVa
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:52:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.84/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.06  % Solved by: fo/fo7.sh
% 0.84/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.06  % done 895 iterations in 0.598s
% 0.84/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.06  % SZS output start Refutation
% 0.84/1.06  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.84/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.06  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.84/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.06  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.84/1.06  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.84/1.06  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.84/1.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.84/1.06  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.84/1.06  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.84/1.06  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.84/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.06  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.84/1.06  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.84/1.06  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.84/1.06  thf(sk_D_type, type, sk_D: $i).
% 0.84/1.06  thf(sk_C_type, type, sk_C: $i).
% 0.84/1.06  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.84/1.06  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.84/1.06  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.84/1.06  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.84/1.06  thf(t36_funct_2, conjecture,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.84/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.06       ( ![D:$i]:
% 0.84/1.06         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.84/1.06             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.84/1.06           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.84/1.06               ( r2_relset_1 @
% 0.84/1.06                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.84/1.06                 ( k6_partfun1 @ A ) ) & 
% 0.84/1.06               ( v2_funct_1 @ C ) ) =>
% 0.84/1.06             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.84/1.06               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.84/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.06    (~( ![A:$i,B:$i,C:$i]:
% 0.84/1.06        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.84/1.06            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.06          ( ![D:$i]:
% 0.84/1.06            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.84/1.06                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.84/1.06              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.84/1.06                  ( r2_relset_1 @
% 0.84/1.06                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.84/1.06                    ( k6_partfun1 @ A ) ) & 
% 0.84/1.06                  ( v2_funct_1 @ C ) ) =>
% 0.84/1.06                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.84/1.06                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.84/1.06    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.84/1.06  thf('0', plain,
% 0.84/1.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('1', plain,
% 0.84/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(redefinition_k1_partfun1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.84/1.06     ( ( ( v1_funct_1 @ E ) & 
% 0.84/1.06         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.84/1.06         ( v1_funct_1 @ F ) & 
% 0.84/1.06         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.84/1.06       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.84/1.06  thf('2', plain,
% 0.84/1.06      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.84/1.06         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.84/1.06          | ~ (v1_funct_1 @ X26)
% 0.84/1.06          | ~ (v1_funct_1 @ X29)
% 0.84/1.06          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.84/1.06          | ((k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 0.84/1.06              = (k5_relat_1 @ X26 @ X29)))),
% 0.84/1.06      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.84/1.06  thf('3', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.06         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.84/1.06            = (k5_relat_1 @ sk_C @ X0))
% 0.84/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.84/1.06          | ~ (v1_funct_1 @ X0)
% 0.84/1.06          | ~ (v1_funct_1 @ sk_C))),
% 0.84/1.06      inference('sup-', [status(thm)], ['1', '2'])).
% 0.84/1.06  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('5', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.06         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.84/1.06            = (k5_relat_1 @ sk_C @ X0))
% 0.84/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.84/1.06          | ~ (v1_funct_1 @ X0))),
% 0.84/1.06      inference('demod', [status(thm)], ['3', '4'])).
% 0.84/1.06  thf('6', plain,
% 0.84/1.06      ((~ (v1_funct_1 @ sk_D)
% 0.84/1.06        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.84/1.06            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['0', '5'])).
% 0.84/1.06  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('8', plain,
% 0.84/1.06      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.84/1.06        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.84/1.06        (k6_partfun1 @ sk_A))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('9', plain,
% 0.84/1.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('10', plain,
% 0.84/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(dt_k1_partfun1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.84/1.06     ( ( ( v1_funct_1 @ E ) & 
% 0.84/1.06         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.84/1.06         ( v1_funct_1 @ F ) & 
% 0.84/1.06         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.84/1.06       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.84/1.06         ( m1_subset_1 @
% 0.84/1.06           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.84/1.06           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.84/1.06  thf('11', plain,
% 0.84/1.06      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.84/1.06         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.84/1.06          | ~ (v1_funct_1 @ X20)
% 0.84/1.06          | ~ (v1_funct_1 @ X23)
% 0.84/1.06          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.84/1.06          | (m1_subset_1 @ (k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23) @ 
% 0.84/1.06             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X25))))),
% 0.84/1.06      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.84/1.06  thf('12', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.06         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.84/1.06           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.84/1.06          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.84/1.06          | ~ (v1_funct_1 @ X1)
% 0.84/1.06          | ~ (v1_funct_1 @ sk_C))),
% 0.84/1.06      inference('sup-', [status(thm)], ['10', '11'])).
% 0.84/1.06  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('14', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.06         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.84/1.06           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.84/1.06          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.84/1.06          | ~ (v1_funct_1 @ X1))),
% 0.84/1.06      inference('demod', [status(thm)], ['12', '13'])).
% 0.84/1.06  thf('15', plain,
% 0.84/1.06      ((~ (v1_funct_1 @ sk_D)
% 0.84/1.06        | (m1_subset_1 @ 
% 0.84/1.06           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.84/1.06           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['9', '14'])).
% 0.84/1.06  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('17', plain,
% 0.84/1.06      ((m1_subset_1 @ 
% 0.84/1.06        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.84/1.06        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.84/1.06      inference('demod', [status(thm)], ['15', '16'])).
% 0.84/1.06  thf(redefinition_r2_relset_1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.06     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.84/1.06         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.06       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.84/1.06  thf('18', plain,
% 0.84/1.06      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.84/1.06         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.84/1.06          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.84/1.06          | ((X15) = (X18))
% 0.84/1.06          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
% 0.84/1.06      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.84/1.06  thf('19', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.84/1.06             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.84/1.06          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.84/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.84/1.06  thf('20', plain,
% 0.84/1.06      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.84/1.06           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.84/1.06        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.84/1.06            = (k6_partfun1 @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['8', '19'])).
% 0.84/1.06  thf(t29_relset_1, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( m1_subset_1 @
% 0.84/1.06       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.84/1.06  thf('21', plain,
% 0.84/1.06      (![X19 : $i]:
% 0.84/1.06         (m1_subset_1 @ (k6_relat_1 @ X19) @ 
% 0.84/1.06          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.84/1.06  thf(redefinition_k6_partfun1, axiom,
% 0.84/1.06    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.84/1.06  thf('22', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.84/1.06      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.84/1.06  thf('23', plain,
% 0.84/1.06      (![X19 : $i]:
% 0.84/1.06         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 0.84/1.06          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.84/1.06      inference('demod', [status(thm)], ['21', '22'])).
% 0.84/1.06  thf('24', plain,
% 0.84/1.06      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.84/1.06         = (k6_partfun1 @ sk_A))),
% 0.84/1.06      inference('demod', [status(thm)], ['20', '23'])).
% 0.84/1.06  thf('25', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.84/1.06      inference('demod', [status(thm)], ['6', '7', '24'])).
% 0.84/1.06  thf(t64_funct_1, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.84/1.06       ( ![B:$i]:
% 0.84/1.06         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.84/1.06           ( ( ( v2_funct_1 @ A ) & 
% 0.84/1.06               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.84/1.06               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.84/1.06             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.84/1.06  thf('26', plain,
% 0.84/1.06      (![X10 : $i, X11 : $i]:
% 0.84/1.06         (~ (v1_relat_1 @ X10)
% 0.84/1.06          | ~ (v1_funct_1 @ X10)
% 0.84/1.06          | ((X10) = (k2_funct_1 @ X11))
% 0.84/1.06          | ((k5_relat_1 @ X10 @ X11) != (k6_relat_1 @ (k2_relat_1 @ X11)))
% 0.84/1.06          | ((k2_relat_1 @ X10) != (k1_relat_1 @ X11))
% 0.84/1.06          | ~ (v2_funct_1 @ X11)
% 0.84/1.06          | ~ (v1_funct_1 @ X11)
% 0.84/1.06          | ~ (v1_relat_1 @ X11))),
% 0.84/1.06      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.84/1.06  thf('27', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.84/1.06      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.84/1.06  thf('28', plain,
% 0.84/1.06      (![X10 : $i, X11 : $i]:
% 0.84/1.06         (~ (v1_relat_1 @ X10)
% 0.84/1.06          | ~ (v1_funct_1 @ X10)
% 0.84/1.06          | ((X10) = (k2_funct_1 @ X11))
% 0.84/1.06          | ((k5_relat_1 @ X10 @ X11) != (k6_partfun1 @ (k2_relat_1 @ X11)))
% 0.84/1.06          | ((k2_relat_1 @ X10) != (k1_relat_1 @ X11))
% 0.84/1.06          | ~ (v2_funct_1 @ X11)
% 0.84/1.06          | ~ (v1_funct_1 @ X11)
% 0.84/1.06          | ~ (v1_relat_1 @ X11))),
% 0.84/1.06      inference('demod', [status(thm)], ['26', '27'])).
% 0.84/1.06  thf('29', plain,
% 0.84/1.06      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.84/1.06        | ~ (v1_relat_1 @ sk_D)
% 0.84/1.06        | ~ (v1_funct_1 @ sk_D)
% 0.84/1.06        | ~ (v2_funct_1 @ sk_D)
% 0.84/1.06        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.84/1.06        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.84/1.06        | ~ (v1_funct_1 @ sk_C)
% 0.84/1.06        | ~ (v1_relat_1 @ sk_C))),
% 0.84/1.06      inference('sup-', [status(thm)], ['25', '28'])).
% 0.84/1.06  thf('30', plain,
% 0.84/1.06      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.84/1.06         = (k6_partfun1 @ sk_A))),
% 0.84/1.06      inference('demod', [status(thm)], ['20', '23'])).
% 0.84/1.06  thf('31', plain,
% 0.84/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(t24_funct_2, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.84/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.06       ( ![D:$i]:
% 0.84/1.06         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.84/1.06             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.84/1.06           ( ( r2_relset_1 @
% 0.84/1.06               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.84/1.06               ( k6_partfun1 @ B ) ) =>
% 0.84/1.06             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.84/1.06  thf('32', plain,
% 0.84/1.06      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.84/1.06         (~ (v1_funct_1 @ X33)
% 0.84/1.06          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.84/1.06          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.84/1.06          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 0.84/1.06               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 0.84/1.06               (k6_partfun1 @ X34))
% 0.84/1.06          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 0.84/1.06          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.84/1.06          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.84/1.07          | ~ (v1_funct_1 @ X36))),
% 0.84/1.07      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.84/1.07  thf('33', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (~ (v1_funct_1 @ X0)
% 0.84/1.07          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.84/1.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.84/1.07          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.84/1.07          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.84/1.07               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.84/1.07               (k6_partfun1 @ sk_A))
% 0.84/1.07          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.84/1.07          | ~ (v1_funct_1 @ sk_C))),
% 0.84/1.07      inference('sup-', [status(thm)], ['31', '32'])).
% 0.84/1.07  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('36', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (~ (v1_funct_1 @ X0)
% 0.84/1.07          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.84/1.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.84/1.07          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.84/1.07          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.84/1.07               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.84/1.07               (k6_partfun1 @ sk_A)))),
% 0.84/1.07      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.84/1.07  thf('37', plain,
% 0.84/1.07      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.84/1.07           (k6_partfun1 @ sk_A))
% 0.84/1.07        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.84/1.07        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.84/1.07        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.84/1.07        | ~ (v1_funct_1 @ sk_D))),
% 0.84/1.07      inference('sup-', [status(thm)], ['30', '36'])).
% 0.84/1.07  thf('38', plain,
% 0.84/1.07      (![X19 : $i]:
% 0.84/1.07         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 0.84/1.07          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.84/1.07      inference('demod', [status(thm)], ['21', '22'])).
% 0.84/1.07  thf('39', plain,
% 0.84/1.07      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.84/1.07         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.84/1.07          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.84/1.07          | (r2_relset_1 @ X16 @ X17 @ X15 @ X18)
% 0.84/1.07          | ((X15) != (X18)))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.84/1.07  thf('40', plain,
% 0.84/1.07      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.84/1.07         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 0.84/1.07          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.84/1.07      inference('simplify', [status(thm)], ['39'])).
% 0.84/1.07  thf('41', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['38', '40'])).
% 0.84/1.07  thf('42', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf(redefinition_k2_relset_1, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i]:
% 0.84/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.07       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.84/1.07  thf('43', plain,
% 0.84/1.07      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.84/1.07         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.84/1.07          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.84/1.07  thf('44', plain,
% 0.84/1.07      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.84/1.07      inference('sup-', [status(thm)], ['42', '43'])).
% 0.84/1.07  thf('45', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.84/1.07      inference('demod', [status(thm)], ['37', '41', '44', '45', '46', '47'])).
% 0.84/1.07  thf('49', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf(cc2_relat_1, axiom,
% 0.84/1.07    (![A:$i]:
% 0.84/1.07     ( ( v1_relat_1 @ A ) =>
% 0.84/1.07       ( ![B:$i]:
% 0.84/1.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.84/1.07  thf('50', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i]:
% 0.84/1.07         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.84/1.07          | (v1_relat_1 @ X0)
% 0.84/1.07          | ~ (v1_relat_1 @ X1))),
% 0.84/1.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.84/1.07  thf('51', plain,
% 0.84/1.07      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.84/1.07      inference('sup-', [status(thm)], ['49', '50'])).
% 0.84/1.07  thf(fc6_relat_1, axiom,
% 0.84/1.07    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.84/1.07  thf('52', plain,
% 0.84/1.07      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.84/1.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.84/1.07  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 0.84/1.07      inference('demod', [status(thm)], ['51', '52'])).
% 0.84/1.07  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('55', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('56', plain,
% 0.84/1.07      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.84/1.07         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.84/1.07          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.84/1.07  thf('57', plain,
% 0.84/1.07      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.84/1.07      inference('sup-', [status(thm)], ['55', '56'])).
% 0.84/1.07  thf('58', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('59', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.84/1.07      inference('sup+', [status(thm)], ['57', '58'])).
% 0.84/1.07  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('61', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('62', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i]:
% 0.84/1.07         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.84/1.07          | (v1_relat_1 @ X0)
% 0.84/1.07          | ~ (v1_relat_1 @ X1))),
% 0.84/1.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.84/1.07  thf('63', plain,
% 0.84/1.07      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.84/1.07      inference('sup-', [status(thm)], ['61', '62'])).
% 0.84/1.07  thf('64', plain,
% 0.84/1.07      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.84/1.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.84/1.07  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.07      inference('demod', [status(thm)], ['63', '64'])).
% 0.84/1.07  thf('66', plain,
% 0.84/1.07      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.84/1.07        | ~ (v2_funct_1 @ sk_D)
% 0.84/1.07        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.84/1.07        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.84/1.07      inference('demod', [status(thm)],
% 0.84/1.07                ['29', '48', '53', '54', '59', '60', '65'])).
% 0.84/1.07  thf('67', plain,
% 0.84/1.07      ((((sk_C) = (k2_funct_1 @ sk_D))
% 0.84/1.07        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.84/1.07        | ~ (v2_funct_1 @ sk_D))),
% 0.84/1.07      inference('simplify', [status(thm)], ['66'])).
% 0.84/1.07  thf('68', plain,
% 0.84/1.07      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.84/1.07         = (k6_partfun1 @ sk_A))),
% 0.84/1.07      inference('demod', [status(thm)], ['20', '23'])).
% 0.84/1.07  thf('69', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf(t30_funct_2, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.07     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.84/1.07         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.84/1.07       ( ![E:$i]:
% 0.84/1.07         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 0.84/1.07             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 0.84/1.07           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.84/1.07               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 0.84/1.07             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 0.84/1.07               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.84/1.07  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.84/1.07  thf(zf_stmt_2, axiom,
% 0.84/1.07    (![C:$i,B:$i]:
% 0.84/1.07     ( ( zip_tseitin_1 @ C @ B ) =>
% 0.84/1.07       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.84/1.07  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.84/1.07  thf(zf_stmt_4, axiom,
% 0.84/1.07    (![E:$i,D:$i]:
% 0.84/1.07     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 0.84/1.07  thf(zf_stmt_5, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.07     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.84/1.07         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.07       ( ![E:$i]:
% 0.84/1.07         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.84/1.07             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.84/1.07           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 0.84/1.07               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 0.84/1.07             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 0.84/1.07  thf('70', plain,
% 0.84/1.07      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.84/1.07         (~ (v1_funct_1 @ X41)
% 0.84/1.07          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 0.84/1.07          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.84/1.07          | (zip_tseitin_0 @ X41 @ X44)
% 0.84/1.07          | ~ (v2_funct_1 @ (k1_partfun1 @ X45 @ X42 @ X42 @ X43 @ X44 @ X41))
% 0.84/1.07          | (zip_tseitin_1 @ X43 @ X42)
% 0.84/1.07          | ((k2_relset_1 @ X45 @ X42 @ X44) != (X42))
% 0.84/1.07          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X42)))
% 0.84/1.07          | ~ (v1_funct_2 @ X44 @ X45 @ X42)
% 0.84/1.07          | ~ (v1_funct_1 @ X44))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.84/1.07  thf('71', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i]:
% 0.84/1.07         (~ (v1_funct_1 @ X0)
% 0.84/1.07          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.84/1.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.84/1.07          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.84/1.07          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.84/1.07          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.84/1.07          | (zip_tseitin_0 @ sk_D @ X0)
% 0.84/1.07          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.84/1.07          | ~ (v1_funct_1 @ sk_D))),
% 0.84/1.07      inference('sup-', [status(thm)], ['69', '70'])).
% 0.84/1.07  thf('72', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('74', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i]:
% 0.84/1.07         (~ (v1_funct_1 @ X0)
% 0.84/1.07          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.84/1.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.84/1.07          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.84/1.07          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.84/1.07          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.84/1.07          | (zip_tseitin_0 @ sk_D @ X0))),
% 0.84/1.07      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.84/1.07  thf('75', plain,
% 0.84/1.07      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.84/1.07        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.84/1.07        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.84/1.07        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.84/1.07        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.84/1.07        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.84/1.07        | ~ (v1_funct_1 @ sk_C))),
% 0.84/1.07      inference('sup-', [status(thm)], ['68', '74'])).
% 0.84/1.07  thf('76', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('77', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('78', plain,
% 0.84/1.07      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.84/1.07         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.84/1.07          | ~ (v1_funct_1 @ X20)
% 0.84/1.07          | ~ (v1_funct_1 @ X23)
% 0.84/1.07          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.84/1.07          | (v1_funct_1 @ (k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23)))),
% 0.84/1.07      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.84/1.07  thf('79', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.07         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 0.84/1.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.84/1.07          | ~ (v1_funct_1 @ X0)
% 0.84/1.07          | ~ (v1_funct_1 @ sk_C))),
% 0.84/1.07      inference('sup-', [status(thm)], ['77', '78'])).
% 0.84/1.07  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('81', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.07         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 0.84/1.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.84/1.07          | ~ (v1_funct_1 @ X0))),
% 0.84/1.07      inference('demod', [status(thm)], ['79', '80'])).
% 0.84/1.07  thf('82', plain,
% 0.84/1.07      ((~ (v1_funct_1 @ sk_D)
% 0.84/1.07        | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)))),
% 0.84/1.07      inference('sup-', [status(thm)], ['76', '81'])).
% 0.84/1.07  thf('83', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('84', plain,
% 0.84/1.07      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.84/1.07         = (k6_partfun1 @ sk_A))),
% 0.84/1.07      inference('demod', [status(thm)], ['20', '23'])).
% 0.84/1.07  thf('85', plain, ((v1_funct_1 @ (k6_partfun1 @ sk_A))),
% 0.84/1.07      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.84/1.07  thf(t71_relat_1, axiom,
% 0.84/1.07    (![A:$i]:
% 0.84/1.07     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.84/1.07       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.84/1.07  thf('86', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 0.84/1.07      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.84/1.07  thf('87', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.84/1.07  thf('88', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.84/1.07      inference('demod', [status(thm)], ['86', '87'])).
% 0.84/1.07  thf(t78_relat_1, axiom,
% 0.84/1.07    (![A:$i]:
% 0.84/1.07     ( ( v1_relat_1 @ A ) =>
% 0.84/1.07       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.84/1.07  thf('89', plain,
% 0.84/1.07      (![X6 : $i]:
% 0.84/1.07         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X6)) @ X6) = (X6))
% 0.84/1.07          | ~ (v1_relat_1 @ X6))),
% 0.84/1.07      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.84/1.07  thf('90', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.84/1.07  thf('91', plain,
% 0.84/1.07      (![X6 : $i]:
% 0.84/1.07         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X6)) @ X6) = (X6))
% 0.84/1.07          | ~ (v1_relat_1 @ X6))),
% 0.84/1.07      inference('demod', [status(thm)], ['89', '90'])).
% 0.84/1.07  thf('92', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.84/1.07            = (k6_partfun1 @ X0))
% 0.84/1.07          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.84/1.07      inference('sup+', [status(thm)], ['88', '91'])).
% 0.84/1.07  thf('93', plain,
% 0.84/1.07      (![X19 : $i]:
% 0.84/1.07         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 0.84/1.07          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.84/1.07      inference('demod', [status(thm)], ['21', '22'])).
% 0.84/1.07  thf('94', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i]:
% 0.84/1.07         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.84/1.07          | (v1_relat_1 @ X0)
% 0.84/1.07          | ~ (v1_relat_1 @ X1))),
% 0.84/1.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.84/1.07  thf('95', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 0.84/1.07          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.84/1.07      inference('sup-', [status(thm)], ['93', '94'])).
% 0.84/1.07  thf('96', plain,
% 0.84/1.07      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.84/1.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.84/1.07  thf('97', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.84/1.07      inference('demod', [status(thm)], ['95', '96'])).
% 0.84/1.07  thf('98', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.84/1.07           = (k6_partfun1 @ X0))),
% 0.84/1.07      inference('demod', [status(thm)], ['92', '97'])).
% 0.84/1.07  thf(t53_funct_1, axiom,
% 0.84/1.07    (![A:$i]:
% 0.84/1.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.84/1.07       ( ( ?[B:$i]:
% 0.84/1.07           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.84/1.07             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 0.84/1.07         ( v2_funct_1 @ A ) ) ))).
% 0.84/1.07  thf('99', plain,
% 0.84/1.07      (![X7 : $i, X8 : $i]:
% 0.84/1.07         (~ (v1_relat_1 @ X7)
% 0.84/1.07          | ~ (v1_funct_1 @ X7)
% 0.84/1.07          | ((k5_relat_1 @ X8 @ X7) != (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.84/1.07          | (v2_funct_1 @ X8)
% 0.84/1.07          | ~ (v1_funct_1 @ X8)
% 0.84/1.07          | ~ (v1_relat_1 @ X8))),
% 0.84/1.07      inference('cnf', [status(esa)], [t53_funct_1])).
% 0.84/1.07  thf('100', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.84/1.07  thf('101', plain,
% 0.84/1.07      (![X7 : $i, X8 : $i]:
% 0.84/1.07         (~ (v1_relat_1 @ X7)
% 0.84/1.07          | ~ (v1_funct_1 @ X7)
% 0.84/1.07          | ((k5_relat_1 @ X8 @ X7) != (k6_partfun1 @ (k1_relat_1 @ X8)))
% 0.84/1.07          | (v2_funct_1 @ X8)
% 0.84/1.07          | ~ (v1_funct_1 @ X8)
% 0.84/1.07          | ~ (v1_relat_1 @ X8))),
% 0.84/1.07      inference('demod', [status(thm)], ['99', '100'])).
% 0.84/1.07  thf('102', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (((k6_partfun1 @ X0)
% 0.84/1.07            != (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ X0))))
% 0.84/1.07          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.84/1.07          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.84/1.07          | (v2_funct_1 @ (k6_partfun1 @ X0))
% 0.84/1.07          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.84/1.07          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.84/1.07      inference('sup-', [status(thm)], ['98', '101'])).
% 0.84/1.07  thf('103', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.84/1.07      inference('demod', [status(thm)], ['86', '87'])).
% 0.84/1.07  thf('104', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.84/1.07      inference('demod', [status(thm)], ['95', '96'])).
% 0.84/1.07  thf('105', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.84/1.07      inference('demod', [status(thm)], ['95', '96'])).
% 0.84/1.07  thf('106', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (((k6_partfun1 @ X0) != (k6_partfun1 @ X0))
% 0.84/1.07          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.84/1.07          | (v2_funct_1 @ (k6_partfun1 @ X0))
% 0.84/1.07          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 0.84/1.07      inference('demod', [status(thm)], ['102', '103', '104', '105'])).
% 0.84/1.07  thf('107', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         ((v2_funct_1 @ (k6_partfun1 @ X0))
% 0.84/1.07          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 0.84/1.07      inference('simplify', [status(thm)], ['106'])).
% 0.84/1.07  thf('108', plain, ((v2_funct_1 @ (k6_partfun1 @ sk_A))),
% 0.84/1.07      inference('sup-', [status(thm)], ['85', '107'])).
% 0.84/1.07  thf('109', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('110', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('111', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('113', plain,
% 0.84/1.07      (((zip_tseitin_0 @ sk_D @ sk_C)
% 0.84/1.07        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.84/1.07        | ((sk_B) != (sk_B)))),
% 0.84/1.07      inference('demod', [status(thm)],
% 0.84/1.07                ['75', '108', '109', '110', '111', '112'])).
% 0.84/1.07  thf('114', plain,
% 0.84/1.07      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 0.84/1.07      inference('simplify', [status(thm)], ['113'])).
% 0.84/1.07  thf('115', plain,
% 0.84/1.07      (![X39 : $i, X40 : $i]:
% 0.84/1.07         (((X39) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X39 @ X40))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.84/1.07  thf('116', plain,
% 0.84/1.07      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.84/1.07      inference('sup-', [status(thm)], ['114', '115'])).
% 0.84/1.07  thf('117', plain, (((sk_A) != (k1_xboole_0))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('118', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 0.84/1.07      inference('simplify_reflect-', [status(thm)], ['116', '117'])).
% 0.84/1.07  thf('119', plain,
% 0.84/1.07      (![X37 : $i, X38 : $i]:
% 0.84/1.07         ((v2_funct_1 @ X38) | ~ (zip_tseitin_0 @ X38 @ X37))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.84/1.07  thf('120', plain, ((v2_funct_1 @ sk_D)),
% 0.84/1.07      inference('sup-', [status(thm)], ['118', '119'])).
% 0.84/1.07  thf('121', plain,
% 0.84/1.07      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 0.84/1.07      inference('demod', [status(thm)], ['67', '120'])).
% 0.84/1.07  thf(t61_funct_1, axiom,
% 0.84/1.07    (![A:$i]:
% 0.84/1.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.84/1.07       ( ( v2_funct_1 @ A ) =>
% 0.84/1.07         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.84/1.07             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.84/1.07           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.84/1.07             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.84/1.07  thf('122', plain,
% 0.84/1.07      (![X9 : $i]:
% 0.84/1.07         (~ (v2_funct_1 @ X9)
% 0.84/1.07          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 0.84/1.07              = (k6_relat_1 @ (k1_relat_1 @ X9)))
% 0.84/1.07          | ~ (v1_funct_1 @ X9)
% 0.84/1.07          | ~ (v1_relat_1 @ X9))),
% 0.84/1.07      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.84/1.07  thf('123', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.84/1.07  thf('124', plain,
% 0.84/1.07      (![X9 : $i]:
% 0.84/1.07         (~ (v2_funct_1 @ X9)
% 0.84/1.07          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 0.84/1.07              = (k6_partfun1 @ (k1_relat_1 @ X9)))
% 0.84/1.07          | ~ (v1_funct_1 @ X9)
% 0.84/1.07          | ~ (v1_relat_1 @ X9))),
% 0.84/1.07      inference('demod', [status(thm)], ['122', '123'])).
% 0.84/1.07  thf('125', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf(t35_funct_2, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i]:
% 0.84/1.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.84/1.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.07       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.84/1.07         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.84/1.07           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.84/1.07             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.84/1.07  thf('126', plain,
% 0.84/1.07      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.84/1.07         (((X46) = (k1_xboole_0))
% 0.84/1.07          | ~ (v1_funct_1 @ X47)
% 0.84/1.07          | ~ (v1_funct_2 @ X47 @ X48 @ X46)
% 0.84/1.07          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X46)))
% 0.84/1.07          | ((k5_relat_1 @ X47 @ (k2_funct_1 @ X47)) = (k6_partfun1 @ X48))
% 0.84/1.07          | ~ (v2_funct_1 @ X47)
% 0.84/1.07          | ((k2_relset_1 @ X48 @ X46 @ X47) != (X46)))),
% 0.84/1.07      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.84/1.07  thf('127', plain,
% 0.84/1.07      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.84/1.07        | ~ (v2_funct_1 @ sk_D)
% 0.84/1.07        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.84/1.07        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.84/1.07        | ~ (v1_funct_1 @ sk_D)
% 0.84/1.07        | ((sk_A) = (k1_xboole_0)))),
% 0.84/1.07      inference('sup-', [status(thm)], ['125', '126'])).
% 0.84/1.07  thf('128', plain,
% 0.84/1.07      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.84/1.07      inference('sup-', [status(thm)], ['42', '43'])).
% 0.84/1.07  thf('129', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('130', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('131', plain,
% 0.84/1.07      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.84/1.07        | ~ (v2_funct_1 @ sk_D)
% 0.84/1.07        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.84/1.07        | ((sk_A) = (k1_xboole_0)))),
% 0.84/1.07      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 0.84/1.07  thf('132', plain, (((sk_A) != (k1_xboole_0))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('133', plain,
% 0.84/1.07      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.84/1.07        | ~ (v2_funct_1 @ sk_D)
% 0.84/1.07        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.84/1.07      inference('simplify_reflect-', [status(thm)], ['131', '132'])).
% 0.84/1.07  thf('134', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.84/1.07      inference('demod', [status(thm)], ['37', '41', '44', '45', '46', '47'])).
% 0.84/1.07  thf('135', plain,
% 0.84/1.07      ((((sk_A) != (sk_A))
% 0.84/1.07        | ~ (v2_funct_1 @ sk_D)
% 0.84/1.07        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.84/1.07      inference('demod', [status(thm)], ['133', '134'])).
% 0.84/1.07  thf('136', plain,
% 0.84/1.07      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.84/1.07        | ~ (v2_funct_1 @ sk_D))),
% 0.84/1.07      inference('simplify', [status(thm)], ['135'])).
% 0.84/1.07  thf('137', plain, ((v2_funct_1 @ sk_D)),
% 0.84/1.07      inference('sup-', [status(thm)], ['118', '119'])).
% 0.84/1.07  thf('138', plain,
% 0.84/1.07      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.84/1.07      inference('demod', [status(thm)], ['136', '137'])).
% 0.84/1.07  thf('139', plain,
% 0.84/1.07      ((((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.84/1.07        | ~ (v1_relat_1 @ sk_D)
% 0.84/1.07        | ~ (v1_funct_1 @ sk_D)
% 0.84/1.07        | ~ (v2_funct_1 @ sk_D))),
% 0.84/1.07      inference('sup+', [status(thm)], ['124', '138'])).
% 0.84/1.07  thf('140', plain, ((v1_relat_1 @ sk_D)),
% 0.84/1.07      inference('demod', [status(thm)], ['51', '52'])).
% 0.84/1.07  thf('141', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('142', plain, ((v2_funct_1 @ sk_D)),
% 0.84/1.07      inference('sup-', [status(thm)], ['118', '119'])).
% 0.84/1.07  thf('143', plain,
% 0.84/1.07      (((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.84/1.07      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 0.84/1.07  thf('144', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.84/1.07      inference('demod', [status(thm)], ['86', '87'])).
% 0.84/1.07  thf('145', plain,
% 0.84/1.07      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 0.84/1.07      inference('sup+', [status(thm)], ['143', '144'])).
% 0.84/1.07  thf('146', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.84/1.07      inference('demod', [status(thm)], ['86', '87'])).
% 0.84/1.07  thf('147', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.84/1.07      inference('demod', [status(thm)], ['145', '146'])).
% 0.84/1.07  thf('148', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 0.84/1.07      inference('demod', [status(thm)], ['121', '147'])).
% 0.84/1.07  thf('149', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.84/1.07      inference('simplify', [status(thm)], ['148'])).
% 0.84/1.07  thf('150', plain,
% 0.84/1.07      (![X9 : $i]:
% 0.84/1.07         (~ (v2_funct_1 @ X9)
% 0.84/1.07          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 0.84/1.07              = (k6_partfun1 @ (k1_relat_1 @ X9)))
% 0.84/1.07          | ~ (v1_funct_1 @ X9)
% 0.84/1.07          | ~ (v1_relat_1 @ X9))),
% 0.84/1.07      inference('demod', [status(thm)], ['122', '123'])).
% 0.84/1.07  thf('151', plain,
% 0.84/1.07      (![X10 : $i, X11 : $i]:
% 0.84/1.07         (~ (v1_relat_1 @ X10)
% 0.84/1.07          | ~ (v1_funct_1 @ X10)
% 0.84/1.07          | ((X10) = (k2_funct_1 @ X11))
% 0.84/1.07          | ((k5_relat_1 @ X10 @ X11) != (k6_partfun1 @ (k2_relat_1 @ X11)))
% 0.84/1.07          | ((k2_relat_1 @ X10) != (k1_relat_1 @ X11))
% 0.84/1.07          | ~ (v2_funct_1 @ X11)
% 0.84/1.07          | ~ (v1_funct_1 @ X11)
% 0.84/1.07          | ~ (v1_relat_1 @ X11))),
% 0.84/1.07      inference('demod', [status(thm)], ['26', '27'])).
% 0.84/1.07  thf('152', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.84/1.07            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.84/1.07          | ~ (v1_relat_1 @ X0)
% 0.84/1.07          | ~ (v1_funct_1 @ X0)
% 0.84/1.07          | ~ (v2_funct_1 @ X0)
% 0.84/1.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.84/1.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.84/1.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.84/1.07          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.84/1.07          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.84/1.07          | ~ (v1_funct_1 @ X0)
% 0.84/1.07          | ~ (v1_relat_1 @ X0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['150', '151'])).
% 0.84/1.07  thf('153', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.84/1.07          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.84/1.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.84/1.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.84/1.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.84/1.07          | ~ (v2_funct_1 @ X0)
% 0.84/1.07          | ~ (v1_funct_1 @ X0)
% 0.84/1.07          | ~ (v1_relat_1 @ X0)
% 0.84/1.07          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.84/1.07              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.84/1.07      inference('simplify', [status(thm)], ['152'])).
% 0.84/1.07  thf('154', plain,
% 0.84/1.07      ((((k6_partfun1 @ (k1_relat_1 @ sk_D))
% 0.84/1.07          != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 0.84/1.07        | ~ (v1_relat_1 @ sk_D)
% 0.84/1.07        | ~ (v1_funct_1 @ sk_D)
% 0.84/1.07        | ~ (v2_funct_1 @ sk_D)
% 0.84/1.07        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 0.84/1.07        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.84/1.07        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 0.84/1.07        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 0.84/1.07        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 0.84/1.07      inference('sup-', [status(thm)], ['149', '153'])).
% 0.84/1.07  thf('155', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.84/1.07      inference('demod', [status(thm)], ['145', '146'])).
% 0.84/1.07  thf('156', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.84/1.07      inference('sup+', [status(thm)], ['57', '58'])).
% 0.84/1.07  thf('157', plain, ((v1_relat_1 @ sk_D)),
% 0.84/1.07      inference('demod', [status(thm)], ['51', '52'])).
% 0.84/1.07  thf('158', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('159', plain, ((v2_funct_1 @ sk_D)),
% 0.84/1.07      inference('sup-', [status(thm)], ['118', '119'])).
% 0.84/1.07  thf('160', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.84/1.07      inference('simplify', [status(thm)], ['148'])).
% 0.84/1.07  thf('161', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.07      inference('demod', [status(thm)], ['63', '64'])).
% 0.84/1.07  thf('162', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.84/1.07      inference('simplify', [status(thm)], ['148'])).
% 0.84/1.07  thf('163', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('164', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.84/1.07      inference('simplify', [status(thm)], ['148'])).
% 0.84/1.07  thf('165', plain, ((v2_funct_1 @ sk_C)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('166', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.84/1.07      inference('demod', [status(thm)], ['37', '41', '44', '45', '46', '47'])).
% 0.84/1.07  thf('167', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.84/1.07      inference('simplify', [status(thm)], ['148'])).
% 0.84/1.07  thf('168', plain,
% 0.84/1.07      (![X9 : $i]:
% 0.84/1.07         (~ (v2_funct_1 @ X9)
% 0.84/1.07          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 0.84/1.07              = (k6_partfun1 @ (k1_relat_1 @ X9)))
% 0.84/1.07          | ~ (v1_funct_1 @ X9)
% 0.84/1.07          | ~ (v1_relat_1 @ X9))),
% 0.84/1.07      inference('demod', [status(thm)], ['122', '123'])).
% 0.84/1.07  thf('169', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('170', plain,
% 0.84/1.07      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.84/1.07         (((X46) = (k1_xboole_0))
% 0.84/1.07          | ~ (v1_funct_1 @ X47)
% 0.84/1.07          | ~ (v1_funct_2 @ X47 @ X48 @ X46)
% 0.84/1.07          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X46)))
% 0.84/1.07          | ((k5_relat_1 @ X47 @ (k2_funct_1 @ X47)) = (k6_partfun1 @ X48))
% 0.84/1.07          | ~ (v2_funct_1 @ X47)
% 0.84/1.07          | ((k2_relset_1 @ X48 @ X46 @ X47) != (X46)))),
% 0.84/1.07      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.84/1.07  thf('171', plain,
% 0.84/1.07      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.91/1.07        | ~ (v2_funct_1 @ sk_C)
% 0.91/1.07        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.91/1.07        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.91/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.07        | ((sk_B) = (k1_xboole_0)))),
% 0.91/1.07      inference('sup-', [status(thm)], ['169', '170'])).
% 0.91/1.07  thf('172', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.91/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.07  thf('173', plain, ((v2_funct_1 @ sk_C)),
% 0.91/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.07  thf('174', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.91/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.07  thf('175', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.07  thf('176', plain,
% 0.91/1.07      ((((sk_B) != (sk_B))
% 0.91/1.07        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.91/1.07        | ((sk_B) = (k1_xboole_0)))),
% 0.91/1.07      inference('demod', [status(thm)], ['171', '172', '173', '174', '175'])).
% 0.91/1.07  thf('177', plain,
% 0.91/1.07      ((((sk_B) = (k1_xboole_0))
% 0.91/1.07        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.91/1.07      inference('simplify', [status(thm)], ['176'])).
% 0.91/1.07  thf('178', plain, (((sk_B) != (k1_xboole_0))),
% 0.91/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.07  thf('179', plain,
% 0.91/1.07      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.91/1.07      inference('simplify_reflect-', [status(thm)], ['177', '178'])).
% 0.91/1.07  thf('180', plain,
% 0.91/1.07      ((((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.91/1.07        | ~ (v1_relat_1 @ sk_C)
% 0.91/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.07        | ~ (v2_funct_1 @ sk_C))),
% 0.91/1.07      inference('sup+', [status(thm)], ['168', '179'])).
% 0.91/1.07  thf('181', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.07      inference('demod', [status(thm)], ['63', '64'])).
% 0.91/1.07  thf('182', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.07  thf('183', plain, ((v2_funct_1 @ sk_C)),
% 0.91/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.07  thf('184', plain,
% 0.91/1.07      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.91/1.07      inference('demod', [status(thm)], ['180', '181', '182', '183'])).
% 0.91/1.07  thf('185', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.91/1.07      inference('demod', [status(thm)], ['86', '87'])).
% 0.91/1.07  thf('186', plain,
% 0.91/1.07      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.91/1.07      inference('sup+', [status(thm)], ['184', '185'])).
% 0.91/1.07  thf('187', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.91/1.07      inference('demod', [status(thm)], ['86', '87'])).
% 0.91/1.07  thf('188', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.91/1.07      inference('demod', [status(thm)], ['186', '187'])).
% 0.91/1.07  thf('189', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.91/1.07      inference('simplify', [status(thm)], ['148'])).
% 0.91/1.07  thf('190', plain,
% 0.91/1.07      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 0.91/1.07        | ((sk_A) != (sk_A))
% 0.91/1.07        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.91/1.07      inference('demod', [status(thm)],
% 0.91/1.07                ['154', '155', '156', '157', '158', '159', '160', '161', 
% 0.91/1.07                 '162', '163', '164', '165', '166', '167', '188', '189'])).
% 0.91/1.07  thf('191', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.91/1.07      inference('simplify', [status(thm)], ['190'])).
% 0.91/1.07  thf('192', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.91/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.07  thf('193', plain, ($false),
% 0.91/1.07      inference('simplify_reflect-', [status(thm)], ['191', '192'])).
% 0.91/1.07  
% 0.91/1.07  % SZS output end Refutation
% 0.91/1.07  
% 0.91/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
