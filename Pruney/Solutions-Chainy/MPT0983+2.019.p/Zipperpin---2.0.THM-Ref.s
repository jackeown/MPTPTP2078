%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0znsF0fEyL

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:03 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 488 expanded)
%              Number of leaves         :   41 ( 160 expanded)
%              Depth                    :   20
%              Number of atoms          : 1202 (9558 expanded)
%              Number of equality atoms :   38 ( 127 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
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
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('18',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
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

thf('23',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( r2_relset_1 @ X34 @ X34 @ ( k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36 ) @ ( k6_relat_1 @ X34 ) )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
        = X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
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
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('32',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != X22 )
      | ( v2_funct_2 @ X23 @ X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('42',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) )
      | ( v2_funct_2 @ X23 @ ( k2_relat_1 @ X23 ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('51',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('52',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['43','46','47','52'])).

thf('54',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('64',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('65',plain,(
    ! [X10: $i] :
      ( ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('71',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('73',plain,(
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

thf('74',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X40 @ X38 @ X38 @ X39 @ X41 @ X37 ) )
      | ( v2_funct_1 @ X41 )
      | ( X39 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X38 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('80',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','57'])).

thf('86',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['84','85'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('87',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('88',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['71','86','88','89'])).

thf('91',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['68','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['58','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0znsF0fEyL
% 0.13/0.36  % Computer   : n024.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 12:47:06 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.83/1.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.83/1.08  % Solved by: fo/fo7.sh
% 0.83/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.08  % done 534 iterations in 0.597s
% 0.83/1.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.83/1.08  % SZS output start Refutation
% 0.83/1.08  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.83/1.08  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.83/1.08  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.83/1.08  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.83/1.08  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.83/1.08  thf(sk_C_type, type, sk_C: $i).
% 0.83/1.08  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.83/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.08  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.83/1.08  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.83/1.08  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.83/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.08  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.83/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.08  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.83/1.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.83/1.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.83/1.08  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.83/1.08  thf(sk_D_type, type, sk_D: $i).
% 0.83/1.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.83/1.08  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.83/1.08  thf(t29_funct_2, conjecture,
% 0.83/1.08    (![A:$i,B:$i,C:$i]:
% 0.83/1.08     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.83/1.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.08       ( ![D:$i]:
% 0.83/1.08         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.83/1.08             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.83/1.08           ( ( r2_relset_1 @
% 0.83/1.08               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.83/1.08               ( k6_partfun1 @ A ) ) =>
% 0.83/1.08             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.83/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.08    (~( ![A:$i,B:$i,C:$i]:
% 0.83/1.08        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.83/1.08            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.08          ( ![D:$i]:
% 0.83/1.08            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.83/1.08                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.83/1.08              ( ( r2_relset_1 @
% 0.83/1.08                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.83/1.08                  ( k6_partfun1 @ A ) ) =>
% 0.83/1.08                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.83/1.08    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.83/1.08  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.83/1.08      inference('split', [status(esa)], ['0'])).
% 0.83/1.08  thf('2', plain,
% 0.83/1.08      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.83/1.08        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.83/1.08        (k6_partfun1 @ sk_A))),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf(redefinition_k6_partfun1, axiom,
% 0.83/1.08    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.83/1.08  thf('3', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.83/1.08      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.83/1.08  thf('4', plain,
% 0.83/1.08      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.83/1.08        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.83/1.08        (k6_relat_1 @ sk_A))),
% 0.83/1.08      inference('demod', [status(thm)], ['2', '3'])).
% 0.83/1.08  thf('5', plain,
% 0.83/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('6', plain,
% 0.83/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf(dt_k1_partfun1, axiom,
% 0.83/1.08    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.83/1.08     ( ( ( v1_funct_1 @ E ) & 
% 0.83/1.08         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.83/1.08         ( v1_funct_1 @ F ) & 
% 0.83/1.08         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.83/1.08       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.83/1.08         ( m1_subset_1 @
% 0.83/1.08           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.83/1.08           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.83/1.08  thf('7', plain,
% 0.83/1.08      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.83/1.08         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.83/1.08          | ~ (v1_funct_1 @ X24)
% 0.83/1.08          | ~ (v1_funct_1 @ X27)
% 0.83/1.08          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.83/1.08          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 0.83/1.08             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 0.83/1.08      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.83/1.08  thf('8', plain,
% 0.83/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.08         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.83/1.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.83/1.08          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.83/1.08          | ~ (v1_funct_1 @ X1)
% 0.83/1.08          | ~ (v1_funct_1 @ sk_C))),
% 0.83/1.08      inference('sup-', [status(thm)], ['6', '7'])).
% 0.83/1.08  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('10', plain,
% 0.83/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.08         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.83/1.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.83/1.08          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.83/1.08          | ~ (v1_funct_1 @ X1))),
% 0.83/1.08      inference('demod', [status(thm)], ['8', '9'])).
% 0.83/1.08  thf('11', plain,
% 0.83/1.08      ((~ (v1_funct_1 @ sk_D)
% 0.83/1.08        | (m1_subset_1 @ 
% 0.83/1.08           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.83/1.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.83/1.08      inference('sup-', [status(thm)], ['5', '10'])).
% 0.83/1.08  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('13', plain,
% 0.83/1.08      ((m1_subset_1 @ 
% 0.83/1.08        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.83/1.08        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.83/1.08      inference('demod', [status(thm)], ['11', '12'])).
% 0.83/1.08  thf(redefinition_r2_relset_1, axiom,
% 0.83/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.08     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.83/1.08         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.08       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.83/1.08  thf('14', plain,
% 0.83/1.08      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.83/1.08         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.83/1.08          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.83/1.08          | ((X18) = (X21))
% 0.83/1.08          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 0.83/1.08      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.83/1.08  thf('15', plain,
% 0.83/1.08      (![X0 : $i]:
% 0.83/1.08         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.83/1.08             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.83/1.08          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.83/1.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.83/1.08      inference('sup-', [status(thm)], ['13', '14'])).
% 0.83/1.08  thf('16', plain,
% 0.83/1.08      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.83/1.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.83/1.08        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.83/1.08            = (k6_relat_1 @ sk_A)))),
% 0.83/1.08      inference('sup-', [status(thm)], ['4', '15'])).
% 0.83/1.08  thf(dt_k6_partfun1, axiom,
% 0.83/1.08    (![A:$i]:
% 0.83/1.08     ( ( m1_subset_1 @
% 0.83/1.08         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.83/1.08       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.83/1.08  thf('17', plain,
% 0.83/1.08      (![X31 : $i]:
% 0.83/1.08         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 0.83/1.08          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.83/1.08      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.83/1.08  thf('18', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.83/1.08      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.83/1.08  thf('19', plain,
% 0.83/1.08      (![X31 : $i]:
% 0.83/1.08         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 0.83/1.08          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.83/1.08      inference('demod', [status(thm)], ['17', '18'])).
% 0.83/1.08  thf('20', plain,
% 0.83/1.08      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.83/1.08         = (k6_relat_1 @ sk_A))),
% 0.83/1.08      inference('demod', [status(thm)], ['16', '19'])).
% 0.83/1.08  thf('21', plain,
% 0.83/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf(t24_funct_2, axiom,
% 0.83/1.08    (![A:$i,B:$i,C:$i]:
% 0.83/1.08     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.83/1.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.08       ( ![D:$i]:
% 0.83/1.08         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.83/1.08             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.83/1.08           ( ( r2_relset_1 @
% 0.83/1.08               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.83/1.08               ( k6_partfun1 @ B ) ) =>
% 0.83/1.08             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.83/1.08  thf('22', plain,
% 0.83/1.08      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.83/1.08         (~ (v1_funct_1 @ X33)
% 0.83/1.08          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.83/1.08          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.83/1.08          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 0.83/1.08               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 0.83/1.08               (k6_partfun1 @ X34))
% 0.83/1.08          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 0.83/1.08          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.83/1.08          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.83/1.08          | ~ (v1_funct_1 @ X36))),
% 0.83/1.08      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.83/1.08  thf('23', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.83/1.08      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.83/1.08  thf('24', plain,
% 0.83/1.08      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.83/1.08         (~ (v1_funct_1 @ X33)
% 0.83/1.08          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.83/1.08          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.83/1.08          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 0.83/1.08               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 0.83/1.08               (k6_relat_1 @ X34))
% 0.83/1.08          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 0.83/1.08          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.83/1.08          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.83/1.08          | ~ (v1_funct_1 @ X36))),
% 0.83/1.08      inference('demod', [status(thm)], ['22', '23'])).
% 0.83/1.08  thf('25', plain,
% 0.83/1.08      (![X0 : $i]:
% 0.83/1.08         (~ (v1_funct_1 @ X0)
% 0.83/1.08          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.83/1.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.83/1.08          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.83/1.08          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.83/1.08               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.83/1.08               (k6_relat_1 @ sk_A))
% 0.83/1.08          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.83/1.08          | ~ (v1_funct_1 @ sk_C))),
% 0.83/1.08      inference('sup-', [status(thm)], ['21', '24'])).
% 0.83/1.08  thf('26', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('28', plain,
% 0.83/1.08      (![X0 : $i]:
% 0.83/1.08         (~ (v1_funct_1 @ X0)
% 0.83/1.08          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.83/1.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.83/1.08          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.83/1.08          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.83/1.08               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.83/1.08               (k6_relat_1 @ sk_A)))),
% 0.83/1.08      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.83/1.08  thf('29', plain,
% 0.83/1.08      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.83/1.08           (k6_relat_1 @ sk_A))
% 0.83/1.08        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.83/1.08        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.83/1.08        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.83/1.08        | ~ (v1_funct_1 @ sk_D))),
% 0.83/1.08      inference('sup-', [status(thm)], ['20', '28'])).
% 0.83/1.08  thf('30', plain,
% 0.83/1.08      (![X31 : $i]:
% 0.83/1.08         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 0.83/1.08          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.83/1.08      inference('demod', [status(thm)], ['17', '18'])).
% 0.83/1.08  thf('31', plain,
% 0.83/1.08      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.83/1.08         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.83/1.08          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.83/1.08          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 0.83/1.08          | ((X18) != (X21)))),
% 0.83/1.08      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.83/1.08  thf('32', plain,
% 0.83/1.08      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.83/1.08         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 0.83/1.08          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.83/1.08      inference('simplify', [status(thm)], ['31'])).
% 0.83/1.08  thf('33', plain,
% 0.83/1.08      (![X0 : $i]:
% 0.83/1.08         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.83/1.08      inference('sup-', [status(thm)], ['30', '32'])).
% 0.83/1.08  thf('34', plain,
% 0.83/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf(redefinition_k2_relset_1, axiom,
% 0.83/1.08    (![A:$i,B:$i,C:$i]:
% 0.83/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.08       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.83/1.08  thf('35', plain,
% 0.83/1.08      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.83/1.08         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.83/1.08          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.83/1.08      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.83/1.08  thf('36', plain,
% 0.83/1.08      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.83/1.08      inference('sup-', [status(thm)], ['34', '35'])).
% 0.83/1.08  thf('37', plain,
% 0.83/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('38', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('39', plain, ((v1_funct_1 @ sk_D)),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('40', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.83/1.08      inference('demod', [status(thm)], ['29', '33', '36', '37', '38', '39'])).
% 0.83/1.08  thf(d3_funct_2, axiom,
% 0.83/1.08    (![A:$i,B:$i]:
% 0.83/1.08     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.83/1.08       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.83/1.08  thf('41', plain,
% 0.83/1.08      (![X22 : $i, X23 : $i]:
% 0.83/1.08         (((k2_relat_1 @ X23) != (X22))
% 0.83/1.08          | (v2_funct_2 @ X23 @ X22)
% 0.83/1.08          | ~ (v5_relat_1 @ X23 @ X22)
% 0.83/1.08          | ~ (v1_relat_1 @ X23))),
% 0.83/1.08      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.83/1.08  thf('42', plain,
% 0.83/1.08      (![X23 : $i]:
% 0.83/1.08         (~ (v1_relat_1 @ X23)
% 0.83/1.08          | ~ (v5_relat_1 @ X23 @ (k2_relat_1 @ X23))
% 0.83/1.08          | (v2_funct_2 @ X23 @ (k2_relat_1 @ X23)))),
% 0.83/1.08      inference('simplify', [status(thm)], ['41'])).
% 0.83/1.08  thf('43', plain,
% 0.83/1.08      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.83/1.08        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.83/1.08        | ~ (v1_relat_1 @ sk_D))),
% 0.83/1.08      inference('sup-', [status(thm)], ['40', '42'])).
% 0.83/1.08  thf('44', plain,
% 0.83/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf(cc2_relset_1, axiom,
% 0.83/1.08    (![A:$i,B:$i,C:$i]:
% 0.83/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.08       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.83/1.08  thf('45', plain,
% 0.83/1.08      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.83/1.08         ((v5_relat_1 @ X12 @ X14)
% 0.83/1.08          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.83/1.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.83/1.08  thf('46', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.83/1.08      inference('sup-', [status(thm)], ['44', '45'])).
% 0.83/1.08  thf('47', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.83/1.08      inference('demod', [status(thm)], ['29', '33', '36', '37', '38', '39'])).
% 0.83/1.08  thf('48', plain,
% 0.83/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf(cc2_relat_1, axiom,
% 0.83/1.08    (![A:$i]:
% 0.83/1.08     ( ( v1_relat_1 @ A ) =>
% 0.83/1.08       ( ![B:$i]:
% 0.83/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.83/1.08  thf('49', plain,
% 0.83/1.08      (![X5 : $i, X6 : $i]:
% 0.83/1.08         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.83/1.08          | (v1_relat_1 @ X5)
% 0.83/1.08          | ~ (v1_relat_1 @ X6))),
% 0.83/1.08      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.83/1.08  thf('50', plain,
% 0.83/1.08      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.83/1.08      inference('sup-', [status(thm)], ['48', '49'])).
% 0.83/1.08  thf(fc6_relat_1, axiom,
% 0.83/1.08    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.83/1.08  thf('51', plain,
% 0.83/1.08      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.83/1.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.83/1.08  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 0.83/1.08      inference('demod', [status(thm)], ['50', '51'])).
% 0.83/1.08  thf('53', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.83/1.08      inference('demod', [status(thm)], ['43', '46', '47', '52'])).
% 0.83/1.08  thf('54', plain,
% 0.83/1.08      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.83/1.08      inference('split', [status(esa)], ['0'])).
% 0.83/1.08  thf('55', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.83/1.08      inference('sup-', [status(thm)], ['53', '54'])).
% 0.83/1.08  thf('56', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.83/1.08      inference('split', [status(esa)], ['0'])).
% 0.83/1.08  thf('57', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.83/1.08      inference('sat_resolution*', [status(thm)], ['55', '56'])).
% 0.83/1.08  thf('58', plain, (~ (v2_funct_1 @ sk_C)),
% 0.83/1.08      inference('simpl_trail', [status(thm)], ['1', '57'])).
% 0.83/1.08  thf('59', plain,
% 0.83/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('60', plain,
% 0.83/1.08      (![X5 : $i, X6 : $i]:
% 0.83/1.08         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.83/1.08          | (v1_relat_1 @ X5)
% 0.83/1.08          | ~ (v1_relat_1 @ X6))),
% 0.83/1.08      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.83/1.08  thf('61', plain,
% 0.83/1.08      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.83/1.08      inference('sup-', [status(thm)], ['59', '60'])).
% 0.83/1.08  thf('62', plain,
% 0.83/1.08      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.83/1.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.83/1.08  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.08      inference('demod', [status(thm)], ['61', '62'])).
% 0.83/1.08  thf(cc1_funct_1, axiom,
% 0.83/1.08    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.83/1.08  thf('64', plain, (![X9 : $i]: ((v1_funct_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.83/1.08      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.83/1.08  thf(cc2_funct_1, axiom,
% 0.83/1.08    (![A:$i]:
% 0.83/1.08     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.83/1.08       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.83/1.08  thf('65', plain,
% 0.83/1.08      (![X10 : $i]:
% 0.83/1.08         ((v2_funct_1 @ X10)
% 0.83/1.08          | ~ (v1_funct_1 @ X10)
% 0.83/1.08          | ~ (v1_relat_1 @ X10)
% 0.83/1.08          | ~ (v1_xboole_0 @ X10))),
% 0.83/1.08      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.83/1.08  thf('66', plain,
% 0.83/1.08      (![X0 : $i]:
% 0.83/1.08         (~ (v1_xboole_0 @ X0)
% 0.83/1.08          | ~ (v1_xboole_0 @ X0)
% 0.83/1.08          | ~ (v1_relat_1 @ X0)
% 0.83/1.08          | (v2_funct_1 @ X0))),
% 0.83/1.08      inference('sup-', [status(thm)], ['64', '65'])).
% 0.83/1.08  thf('67', plain,
% 0.83/1.08      (![X0 : $i]:
% 0.83/1.08         ((v2_funct_1 @ X0) | ~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.08      inference('simplify', [status(thm)], ['66'])).
% 0.83/1.08  thf('68', plain, ((~ (v1_xboole_0 @ sk_C) | (v2_funct_1 @ sk_C))),
% 0.83/1.08      inference('sup-', [status(thm)], ['63', '67'])).
% 0.83/1.08  thf('69', plain,
% 0.83/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf(cc1_subset_1, axiom,
% 0.83/1.08    (![A:$i]:
% 0.83/1.08     ( ( v1_xboole_0 @ A ) =>
% 0.83/1.08       ( ![B:$i]:
% 0.83/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.83/1.08  thf('70', plain,
% 0.83/1.08      (![X3 : $i, X4 : $i]:
% 0.83/1.08         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.83/1.08          | (v1_xboole_0 @ X3)
% 0.83/1.08          | ~ (v1_xboole_0 @ X4))),
% 0.83/1.08      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.83/1.08  thf('71', plain,
% 0.83/1.08      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.83/1.08      inference('sup-', [status(thm)], ['69', '70'])).
% 0.83/1.08  thf('72', plain,
% 0.83/1.08      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.83/1.08         = (k6_relat_1 @ sk_A))),
% 0.83/1.08      inference('demod', [status(thm)], ['16', '19'])).
% 0.83/1.08  thf('73', plain,
% 0.83/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf(t26_funct_2, axiom,
% 0.83/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.08     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.83/1.08         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.08       ( ![E:$i]:
% 0.83/1.08         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.83/1.08             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.83/1.08           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.83/1.08             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.83/1.08               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.83/1.08  thf('74', plain,
% 0.83/1.08      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.83/1.08         (~ (v1_funct_1 @ X37)
% 0.83/1.08          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.83/1.08          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.83/1.08          | ~ (v2_funct_1 @ (k1_partfun1 @ X40 @ X38 @ X38 @ X39 @ X41 @ X37))
% 0.83/1.08          | (v2_funct_1 @ X41)
% 0.83/1.08          | ((X39) = (k1_xboole_0))
% 0.83/1.08          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X38)))
% 0.83/1.08          | ~ (v1_funct_2 @ X41 @ X40 @ X38)
% 0.83/1.08          | ~ (v1_funct_1 @ X41))),
% 0.83/1.08      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.83/1.08  thf('75', plain,
% 0.83/1.08      (![X0 : $i, X1 : $i]:
% 0.83/1.08         (~ (v1_funct_1 @ X0)
% 0.83/1.08          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.83/1.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.83/1.08          | ((sk_A) = (k1_xboole_0))
% 0.83/1.08          | (v2_funct_1 @ X0)
% 0.83/1.08          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.83/1.08          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.83/1.08          | ~ (v1_funct_1 @ sk_D))),
% 0.83/1.08      inference('sup-', [status(thm)], ['73', '74'])).
% 0.83/1.08  thf('76', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('77', plain, ((v1_funct_1 @ sk_D)),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('78', plain,
% 0.83/1.08      (![X0 : $i, X1 : $i]:
% 0.83/1.08         (~ (v1_funct_1 @ X0)
% 0.83/1.08          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.83/1.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.83/1.08          | ((sk_A) = (k1_xboole_0))
% 0.83/1.08          | (v2_funct_1 @ X0)
% 0.83/1.08          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.83/1.08      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.83/1.08  thf('79', plain,
% 0.83/1.08      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.83/1.08        | (v2_funct_1 @ sk_C)
% 0.83/1.08        | ((sk_A) = (k1_xboole_0))
% 0.83/1.08        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.83/1.08        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.83/1.08        | ~ (v1_funct_1 @ sk_C))),
% 0.83/1.08      inference('sup-', [status(thm)], ['72', '78'])).
% 0.83/1.08  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.83/1.08  thf('80', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 0.83/1.08      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.83/1.08  thf('81', plain,
% 0.83/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('82', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('84', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.83/1.08      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.83/1.08  thf('85', plain, (~ (v2_funct_1 @ sk_C)),
% 0.83/1.08      inference('simpl_trail', [status(thm)], ['1', '57'])).
% 0.83/1.08  thf('86', plain, (((sk_A) = (k1_xboole_0))),
% 0.83/1.08      inference('clc', [status(thm)], ['84', '85'])).
% 0.83/1.08  thf(t113_zfmisc_1, axiom,
% 0.83/1.08    (![A:$i,B:$i]:
% 0.83/1.08     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.83/1.08       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.83/1.08  thf('87', plain,
% 0.83/1.08      (![X1 : $i, X2 : $i]:
% 0.83/1.08         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.83/1.08      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.83/1.08  thf('88', plain,
% 0.83/1.08      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.83/1.08      inference('simplify', [status(thm)], ['87'])).
% 0.83/1.08  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.83/1.08  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.08  thf('90', plain, ((v1_xboole_0 @ sk_C)),
% 0.83/1.08      inference('demod', [status(thm)], ['71', '86', '88', '89'])).
% 0.83/1.08  thf('91', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.08      inference('demod', [status(thm)], ['68', '90'])).
% 0.83/1.08  thf('92', plain, ($false), inference('demod', [status(thm)], ['58', '91'])).
% 0.83/1.08  
% 0.83/1.08  % SZS output end Refutation
% 0.83/1.08  
% 0.91/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
