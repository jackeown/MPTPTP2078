%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3rnrQ0VHJK

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:03 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 737 expanded)
%              Number of leaves         :   39 ( 234 expanded)
%              Depth                    :   19
%              Number of atoms          : 1213 (14850 expanded)
%              Number of equality atoms :   50 ( 218 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('0',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('17',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('18',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
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

thf('22',plain,(
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

thf('23',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
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
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('31',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 )
      | ( X22 != X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('32',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['29','33','36','37','38','39'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('41',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_relat_1 @ X27 )
       != X26 )
      | ( v2_funct_2 @ X27 @ X26 )
      | ~ ( v5_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('42',plain,(
    ! [X27: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v5_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
      | ( v2_funct_2 @ X27 @ ( k2_relat_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['29','33','36','37','38','39'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('49',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['43','46','47','50'])).

thf('52',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('58',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('60',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('64',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X44 @ X42 @ X42 @ X43 @ X45 @ X41 ) )
      | ( v2_funct_1 @ X45 )
      | ( X43 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X42 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('70',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','55'])).

thf('76',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['74','75'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('77',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('78',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('79',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['74','75'])).

thf('81',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('82',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['61','76','78','79','80','81'])).

thf('83',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('84',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('86',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('88',plain,(
    r1_tarski @ ( k6_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('94',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['56','82','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3rnrQ0VHJK
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:03:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.86  % Solved by: fo/fo7.sh
% 0.68/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.86  % done 670 iterations in 0.399s
% 0.68/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.86  % SZS output start Refutation
% 0.68/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.86  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.86  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.68/0.86  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.68/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.68/0.86  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.68/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.86  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.68/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.86  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.68/0.86  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.68/0.86  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.68/0.86  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.68/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.86  thf(sk_D_type, type, sk_D: $i).
% 0.68/0.86  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.68/0.86  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.68/0.86  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.68/0.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.68/0.86  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.68/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.86  thf(t29_funct_2, conjecture,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.68/0.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.68/0.86       ( ![D:$i]:
% 0.68/0.86         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.68/0.86             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.68/0.86           ( ( r2_relset_1 @
% 0.68/0.86               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.68/0.86               ( k6_partfun1 @ A ) ) =>
% 0.68/0.86             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.68/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.86    (~( ![A:$i,B:$i,C:$i]:
% 0.68/0.86        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.68/0.86            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.68/0.86          ( ![D:$i]:
% 0.68/0.86            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.68/0.86                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.68/0.86              ( ( r2_relset_1 @
% 0.68/0.86                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.68/0.86                  ( k6_partfun1 @ A ) ) =>
% 0.68/0.86                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.68/0.86    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.68/0.86  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.68/0.86      inference('split', [status(esa)], ['0'])).
% 0.68/0.86  thf('2', plain,
% 0.68/0.86      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.68/0.86        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.68/0.86        (k6_partfun1 @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(redefinition_k6_partfun1, axiom,
% 0.68/0.86    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.68/0.86  thf('3', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.68/0.86      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.68/0.86  thf('4', plain,
% 0.68/0.86      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.68/0.86        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.68/0.86        (k6_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['2', '3'])).
% 0.68/0.86  thf('5', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('6', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(dt_k1_partfun1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.68/0.86     ( ( ( v1_funct_1 @ E ) & 
% 0.68/0.86         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.68/0.86         ( v1_funct_1 @ F ) & 
% 0.68/0.86         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.68/0.86       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.68/0.86         ( m1_subset_1 @
% 0.68/0.86           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.68/0.86           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.68/0.86  thf('7', plain,
% 0.68/0.86      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.68/0.86         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.68/0.86          | ~ (v1_funct_1 @ X28)
% 0.68/0.86          | ~ (v1_funct_1 @ X31)
% 0.68/0.86          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.68/0.86          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 0.68/0.86             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 0.68/0.86      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.68/0.86  thf('8', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.68/0.86           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.68/0.86          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.68/0.86          | ~ (v1_funct_1 @ X1)
% 0.68/0.86          | ~ (v1_funct_1 @ sk_C))),
% 0.68/0.86      inference('sup-', [status(thm)], ['6', '7'])).
% 0.68/0.86  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('10', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.68/0.86           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.68/0.86          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.68/0.86          | ~ (v1_funct_1 @ X1))),
% 0.68/0.86      inference('demod', [status(thm)], ['8', '9'])).
% 0.68/0.86  thf('11', plain,
% 0.68/0.86      ((~ (v1_funct_1 @ sk_D)
% 0.68/0.86        | (m1_subset_1 @ 
% 0.68/0.86           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.68/0.86           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.68/0.86      inference('sup-', [status(thm)], ['5', '10'])).
% 0.68/0.86  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('13', plain,
% 0.68/0.86      ((m1_subset_1 @ 
% 0.68/0.86        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.68/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.68/0.86      inference('demod', [status(thm)], ['11', '12'])).
% 0.68/0.86  thf(redefinition_r2_relset_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.86     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.68/0.86         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.68/0.86       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.68/0.86  thf('14', plain,
% 0.68/0.86      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.68/0.86         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.68/0.86          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.68/0.86          | ((X22) = (X25))
% 0.68/0.86          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 0.68/0.86      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.68/0.86  thf('15', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.68/0.86             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.68/0.86          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.68/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.68/0.86      inference('sup-', [status(thm)], ['13', '14'])).
% 0.68/0.86  thf('16', plain,
% 0.68/0.86      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.68/0.86           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.68/0.86        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.68/0.86            = (k6_relat_1 @ sk_A)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['4', '15'])).
% 0.68/0.86  thf(dt_k6_partfun1, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( m1_subset_1 @
% 0.68/0.86         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.68/0.86       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.68/0.86  thf('17', plain,
% 0.68/0.86      (![X35 : $i]:
% 0.68/0.86         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 0.68/0.86          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.68/0.86      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.68/0.86  thf('18', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.68/0.86      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.68/0.86  thf('19', plain,
% 0.68/0.86      (![X35 : $i]:
% 0.68/0.86         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 0.68/0.86          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.68/0.86      inference('demod', [status(thm)], ['17', '18'])).
% 0.68/0.86  thf('20', plain,
% 0.68/0.86      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.68/0.86         = (k6_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['16', '19'])).
% 0.68/0.86  thf('21', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(t24_funct_2, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.68/0.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.68/0.86       ( ![D:$i]:
% 0.68/0.86         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.68/0.86             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.68/0.86           ( ( r2_relset_1 @
% 0.68/0.86               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.68/0.86               ( k6_partfun1 @ B ) ) =>
% 0.68/0.86             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.68/0.86  thf('22', plain,
% 0.68/0.86      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.68/0.86         (~ (v1_funct_1 @ X37)
% 0.68/0.86          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.68/0.86          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.68/0.86          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 0.68/0.86               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 0.68/0.86               (k6_partfun1 @ X38))
% 0.68/0.86          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 0.68/0.86          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 0.68/0.86          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 0.68/0.86          | ~ (v1_funct_1 @ X40))),
% 0.68/0.86      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.68/0.86  thf('23', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.68/0.86      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.68/0.86  thf('24', plain,
% 0.68/0.86      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.68/0.86         (~ (v1_funct_1 @ X37)
% 0.68/0.86          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.68/0.86          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.68/0.86          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 0.68/0.86               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 0.68/0.86               (k6_relat_1 @ X38))
% 0.68/0.86          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 0.68/0.86          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 0.68/0.86          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 0.68/0.86          | ~ (v1_funct_1 @ X40))),
% 0.68/0.86      inference('demod', [status(thm)], ['22', '23'])).
% 0.68/0.86  thf('25', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (~ (v1_funct_1 @ X0)
% 0.68/0.86          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.68/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.68/0.86          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.68/0.86          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.68/0.86               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.68/0.86               (k6_relat_1 @ sk_A))
% 0.68/0.86          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.68/0.86          | ~ (v1_funct_1 @ sk_C))),
% 0.68/0.86      inference('sup-', [status(thm)], ['21', '24'])).
% 0.68/0.86  thf('26', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('28', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (~ (v1_funct_1 @ X0)
% 0.68/0.86          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.68/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.68/0.86          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.68/0.86          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.68/0.86               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.68/0.86               (k6_relat_1 @ sk_A)))),
% 0.68/0.86      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.68/0.86  thf('29', plain,
% 0.68/0.86      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.68/0.86           (k6_relat_1 @ sk_A))
% 0.68/0.86        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.68/0.86        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.68/0.86        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.68/0.86        | ~ (v1_funct_1 @ sk_D))),
% 0.68/0.86      inference('sup-', [status(thm)], ['20', '28'])).
% 0.68/0.86  thf('30', plain,
% 0.68/0.86      (![X35 : $i]:
% 0.68/0.86         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 0.68/0.86          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.68/0.86      inference('demod', [status(thm)], ['17', '18'])).
% 0.68/0.86  thf('31', plain,
% 0.68/0.86      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.68/0.86         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.68/0.86          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.68/0.86          | (r2_relset_1 @ X23 @ X24 @ X22 @ X25)
% 0.68/0.86          | ((X22) != (X25)))),
% 0.68/0.86      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.68/0.86  thf('32', plain,
% 0.68/0.86      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.68/0.86         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 0.68/0.86          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.68/0.86      inference('simplify', [status(thm)], ['31'])).
% 0.68/0.86  thf('33', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['30', '32'])).
% 0.68/0.86  thf('34', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(redefinition_k2_relset_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.86       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.68/0.86  thf('35', plain,
% 0.68/0.86      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.68/0.86         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.68/0.86          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.68/0.86      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.68/0.86  thf('36', plain,
% 0.68/0.86      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.68/0.86      inference('sup-', [status(thm)], ['34', '35'])).
% 0.68/0.86  thf('37', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('38', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('39', plain, ((v1_funct_1 @ sk_D)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('40', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['29', '33', '36', '37', '38', '39'])).
% 0.68/0.86  thf(d3_funct_2, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.68/0.86       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.68/0.86  thf('41', plain,
% 0.68/0.86      (![X26 : $i, X27 : $i]:
% 0.68/0.86         (((k2_relat_1 @ X27) != (X26))
% 0.68/0.86          | (v2_funct_2 @ X27 @ X26)
% 0.68/0.86          | ~ (v5_relat_1 @ X27 @ X26)
% 0.68/0.86          | ~ (v1_relat_1 @ X27))),
% 0.68/0.86      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.68/0.86  thf('42', plain,
% 0.68/0.86      (![X27 : $i]:
% 0.68/0.86         (~ (v1_relat_1 @ X27)
% 0.68/0.86          | ~ (v5_relat_1 @ X27 @ (k2_relat_1 @ X27))
% 0.68/0.86          | (v2_funct_2 @ X27 @ (k2_relat_1 @ X27)))),
% 0.68/0.86      inference('simplify', [status(thm)], ['41'])).
% 0.68/0.86  thf('43', plain,
% 0.68/0.86      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.68/0.86        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.68/0.86        | ~ (v1_relat_1 @ sk_D))),
% 0.68/0.86      inference('sup-', [status(thm)], ['40', '42'])).
% 0.68/0.86  thf('44', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(cc2_relset_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.86       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.68/0.86  thf('45', plain,
% 0.68/0.86      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.86         ((v5_relat_1 @ X16 @ X18)
% 0.68/0.86          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.68/0.86      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.68/0.86  thf('46', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.68/0.86      inference('sup-', [status(thm)], ['44', '45'])).
% 0.68/0.86  thf('47', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['29', '33', '36', '37', '38', '39'])).
% 0.68/0.86  thf('48', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(cc1_relset_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.86       ( v1_relat_1 @ C ) ))).
% 0.68/0.86  thf('49', plain,
% 0.68/0.86      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.68/0.86         ((v1_relat_1 @ X13)
% 0.68/0.86          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.68/0.86      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.68/0.86  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 0.68/0.86      inference('sup-', [status(thm)], ['48', '49'])).
% 0.68/0.86  thf('51', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.68/0.86      inference('demod', [status(thm)], ['43', '46', '47', '50'])).
% 0.68/0.86  thf('52', plain,
% 0.68/0.86      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.68/0.86      inference('split', [status(esa)], ['0'])).
% 0.68/0.86  thf('53', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.68/0.86      inference('sup-', [status(thm)], ['51', '52'])).
% 0.68/0.86  thf('54', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.68/0.86      inference('split', [status(esa)], ['0'])).
% 0.68/0.86  thf('55', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.68/0.86      inference('sat_resolution*', [status(thm)], ['53', '54'])).
% 0.68/0.86  thf('56', plain, (~ (v2_funct_1 @ sk_C)),
% 0.68/0.86      inference('simpl_trail', [status(thm)], ['1', '55'])).
% 0.68/0.86  thf('57', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(t3_subset, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.68/0.86  thf('58', plain,
% 0.68/0.86      (![X7 : $i, X8 : $i]:
% 0.68/0.86         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.86  thf('59', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.68/0.86      inference('sup-', [status(thm)], ['57', '58'])).
% 0.68/0.86  thf(d10_xboole_0, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.86  thf('60', plain,
% 0.68/0.86      (![X0 : $i, X2 : $i]:
% 0.68/0.86         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.68/0.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.86  thf('61', plain,
% 0.68/0.86      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 0.68/0.86        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['59', '60'])).
% 0.68/0.86  thf('62', plain,
% 0.68/0.86      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.68/0.86         = (k6_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['16', '19'])).
% 0.68/0.86  thf('63', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(t26_funct_2, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.86     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.68/0.86         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.68/0.86       ( ![E:$i]:
% 0.68/0.86         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.68/0.86             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.68/0.86           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.68/0.86             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.68/0.86               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.68/0.86  thf('64', plain,
% 0.68/0.86      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.68/0.86         (~ (v1_funct_1 @ X41)
% 0.68/0.86          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 0.68/0.86          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.68/0.86          | ~ (v2_funct_1 @ (k1_partfun1 @ X44 @ X42 @ X42 @ X43 @ X45 @ X41))
% 0.68/0.86          | (v2_funct_1 @ X45)
% 0.68/0.86          | ((X43) = (k1_xboole_0))
% 0.68/0.86          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X42)))
% 0.68/0.86          | ~ (v1_funct_2 @ X45 @ X44 @ X42)
% 0.68/0.86          | ~ (v1_funct_1 @ X45))),
% 0.68/0.86      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.68/0.86  thf('65', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         (~ (v1_funct_1 @ X0)
% 0.68/0.86          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.68/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.68/0.86          | ((sk_A) = (k1_xboole_0))
% 0.68/0.86          | (v2_funct_1 @ X0)
% 0.68/0.86          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.68/0.86          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.68/0.86          | ~ (v1_funct_1 @ sk_D))),
% 0.68/0.86      inference('sup-', [status(thm)], ['63', '64'])).
% 0.68/0.86  thf('66', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('67', plain, ((v1_funct_1 @ sk_D)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('68', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         (~ (v1_funct_1 @ X0)
% 0.68/0.86          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.68/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.68/0.86          | ((sk_A) = (k1_xboole_0))
% 0.68/0.86          | (v2_funct_1 @ X0)
% 0.68/0.86          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.68/0.86      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.68/0.86  thf('69', plain,
% 0.68/0.86      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.68/0.86        | (v2_funct_1 @ sk_C)
% 0.68/0.86        | ((sk_A) = (k1_xboole_0))
% 0.68/0.86        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.68/0.86        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.68/0.86        | ~ (v1_funct_1 @ sk_C))),
% 0.68/0.86      inference('sup-', [status(thm)], ['62', '68'])).
% 0.68/0.86  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.68/0.86  thf('70', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 0.68/0.86      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.68/0.86  thf('71', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('72', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('74', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.68/0.86      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 0.68/0.86  thf('75', plain, (~ (v2_funct_1 @ sk_C)),
% 0.68/0.86      inference('simpl_trail', [status(thm)], ['1', '55'])).
% 0.68/0.86  thf('76', plain, (((sk_A) = (k1_xboole_0))),
% 0.68/0.86      inference('clc', [status(thm)], ['74', '75'])).
% 0.68/0.86  thf(t113_zfmisc_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.68/0.86       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.68/0.86  thf('77', plain,
% 0.68/0.86      (![X5 : $i, X6 : $i]:
% 0.68/0.86         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.68/0.86  thf('78', plain,
% 0.68/0.86      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.68/0.86      inference('simplify', [status(thm)], ['77'])).
% 0.68/0.86  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.68/0.86  thf('79', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.68/0.86      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.86  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 0.68/0.86      inference('clc', [status(thm)], ['74', '75'])).
% 0.68/0.86  thf('81', plain,
% 0.68/0.86      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.68/0.86      inference('simplify', [status(thm)], ['77'])).
% 0.68/0.86  thf('82', plain, (((k1_xboole_0) = (sk_C))),
% 0.68/0.86      inference('demod', [status(thm)], ['61', '76', '78', '79', '80', '81'])).
% 0.68/0.86  thf('83', plain,
% 0.68/0.86      (![X5 : $i, X6 : $i]:
% 0.68/0.86         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.68/0.86  thf('84', plain,
% 0.68/0.86      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.86      inference('simplify', [status(thm)], ['83'])).
% 0.68/0.86  thf('85', plain,
% 0.68/0.86      (![X35 : $i]:
% 0.68/0.86         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 0.68/0.86          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.68/0.86      inference('demod', [status(thm)], ['17', '18'])).
% 0.68/0.86  thf('86', plain,
% 0.68/0.86      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.68/0.86      inference('sup+', [status(thm)], ['84', '85'])).
% 0.68/0.86  thf('87', plain,
% 0.68/0.86      (![X7 : $i, X8 : $i]:
% 0.68/0.86         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.86  thf('88', plain, ((r1_tarski @ (k6_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.68/0.86      inference('sup-', [status(thm)], ['86', '87'])).
% 0.68/0.86  thf('89', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.68/0.86      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.86  thf('90', plain,
% 0.68/0.86      (![X0 : $i, X2 : $i]:
% 0.68/0.86         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.68/0.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.86  thf('91', plain,
% 0.68/0.86      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['89', '90'])).
% 0.68/0.86  thf('92', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['88', '91'])).
% 0.68/0.86  thf('93', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 0.68/0.86      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.68/0.86  thf('94', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.68/0.86      inference('sup+', [status(thm)], ['92', '93'])).
% 0.68/0.86  thf('95', plain, ($false),
% 0.68/0.86      inference('demod', [status(thm)], ['56', '82', '94'])).
% 0.68/0.86  
% 0.68/0.86  % SZS output end Refutation
% 0.68/0.86  
% 0.68/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
